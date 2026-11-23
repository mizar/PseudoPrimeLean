/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2857341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2825341184 :
    ThetaLowerSegment 2825341184 2825472256 (282528446994899 / 100000) (11301662515199 / 4000) := by
  exact
    packedTile65536 2825341184 2825472256 14 6027 53153 31 _ _ (544047 / 25000) (2176191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2825472256 :
    ThetaLowerSegment 2825472256 2825603328 (11301662515199 / 4000) (141277321988049 / 50000) := by
  exact
    packedTile65536 2825472256 2825603328 14 6011 53155 31 _ _ (2176193 / 100000) (544049 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2825603328 :
    ThetaLowerSegment 2825603328 2825734400 (141277321988049 / 50000)
      (282567733801053 / 100000) := by
  exact
    packedTile65536 2825603328 2825734400 14 6015 53156 31 _ _ (2176197 / 100000) (10881 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2825734400 :
    ThetaLowerSegment 2825734400 2825865472 (282567733801053 / 100000)
      (56516182576073 / 20000) := by
  exact
    packedTile65536 2825734400 2825865472 14 6056 53157 31 _ _ (1088101 / 50000) (435241 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2825865472 :
    ThetaLowerSegment 2825865472 2825996544 (56516182576073 / 20000)
      (282594126809269 / 100000) := by
  exact
    packedTile65536 2825865472 2825996544 14 6072 53158 31 _ _ (2176207 / 100000) (217621 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2825996544 :
    ThetaLowerSegment 2825996544 2826127616 (282594126809269 / 100000)
      (282607036092921 / 100000) := by
  exact
    packedTile65536 2825996544 2826127616 14 5932 53160 31 _ _ (2176211 / 100000) (1088107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2826127616 :
    ThetaLowerSegment 2826127616 2826258688 (282607036092921 / 100000)
      (282619958463529 / 100000) := by
  exact
    packedTile65536 2826127616 2826258688 14 5938 53161 31 _ _ (272027 / 12500) (2176219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2826258688 :
    ThetaLowerSegment 2826258688 2826389760 (282619958463529 / 100000)
      (282633098479889 / 100000) := by
  exact
    packedTile65536 2826258688 2826389760 14 6038 53162 31 _ _ (108811 / 5000) (2176223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2826389760 :
    ThetaLowerSegment 2826389760 2826520832 (282633098479889 / 100000)
      (70661575409241 / 25000) := by
  exact
    packedTile65536 2826389760 2826520832 14 6067 53163 31 _ _ (87049 / 4000) (544057 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2826520832 :
    ThetaLowerSegment 2826520832 2826651904 (70661575409241 / 25000) (141329708887587 / 50000) := by
  exact
    packedTile65536 2826520832 2826651904 14 6027 53165 31 _ _ (217623 / 10000) (2176233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2826651904 :
    ThetaLowerSegment 2826651904 2826782976 (141329708887587 / 50000)
      (141336311581543 / 50000) := by
  exact
    packedTile65536 2826651904 2826782976 14 6068 53166 31 _ _ (1088117 / 50000) (2176237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2826782976 :
    ThetaLowerSegment 2826782976 2826914048 (141336311581543 / 50000) (14134278154009 / 5000) := by
  exact
    packedTile65536 2826782976 2826914048 14 5946 53167 31 _ _ (2176239 / 100000) (1088121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2826914048 :
    ThetaLowerSegment 2826914048 2827045120 (14134278154009 / 5000) (14134929939087 / 5000) := by
  exact
    packedTile65536 2826914048 2827045120 14 5990 53168 31 _ _ (544061 / 25000) (2176247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2827045120 :
    ThetaLowerSegment 2827045120 2827176192 (14134929939087 / 5000) (70677932565543 / 25000) := by
  exact
    packedTile65536 2827045120 2827176192 14 6034 53169 31 _ _ (272031 / 12500) (2176251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2827176192 :
    ThetaLowerSegment 2827176192 2827307264 (70677932565543 / 25000) (56544962343791 / 20000) := by
  exact
    packedTile65536 2827176192 2827307264 14 6011 53171 31 _ _ (2176253 / 100000) (68008 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2827307264 :
    ThetaLowerSegment 2827307264 2827438336 (56544962343791 / 20000)
      (282738113007851 / 100000) := by
  exact
    packedTile65536 2827307264 2827438336 14 6112 53172 31 _ _ (1088129 / 50000) (2176261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2827438336 :
    ThetaLowerSegment 2827438336 2827569408 (282738113007851 / 100000)
      (282751203223781 / 100000) := by
  exact
    packedTile65536 2827438336 2827569408 14 6015 53173 31 _ _ (1088131 / 50000) (435253 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2827569408 :
    ThetaLowerSegment 2827569408 2827700480 (282751203223781 / 100000)
      (141382164145029 / 50000) := by
  exact
    packedTile65536 2827569408 2827700480 14 6031 53174 31 _ _ (2176267 / 100000) (217627 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2827700480 :
    ThetaLowerSegment 2827700480 2827831552 (141382164145029 / 50000)
      (282777348919451 / 100000) := by
  exact
    packedTile65536 2827700480 2827831552 14 5983 53176 31 _ _ (2176271 / 100000) (1088137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2827831552 :
    ThetaLowerSegment 2827831552 2827962624 (282777348919451 / 100000)
      (56558096113767 / 20000) := by
  exact
    packedTile65536 2827831552 2827962624 14 6034 53177 31 _ _ (544069 / 25000) (2176279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2827962624 :
    ThetaLowerSegment 2827962624 2828093696 (56558096113767 / 20000) (2828036797131 / 1000) := by
  exact
    packedTile65536 2827962624 2828093696 14 6065 53178 31 _ _ (2176281 / 100000) (544071 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2828093696 :
    ThetaLowerSegment 2828093696 2828224768 (2828036797131 / 1000) (28281687235277 / 10000) := by
  exact
    packedTile65536 2828093696 2828224768 14 6062 53179 31 _ _ (435257 / 20000) (68009 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2828224768 :
    ThetaLowerSegment 2828224768 2828355840 (28281687235277 / 10000) (14141498789743 / 5000) := by
  exact
    packedTile65536 2828224768 2828355840 14 6021 53181 31 _ _ (217629 / 10000) (2176293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2828355840 :
    ThetaLowerSegment 2828355840 2828486912 (14141498789743 / 5000) (2828431902581 / 1000) := by
  exact
    packedTile65536 2828355840 2828486912 14 6072 53182 31 _ _ (435259 / 20000) (1088149 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2828486912 :
    ThetaLowerSegment 2828486912 2828617984 (2828431902581 / 1000) (282856224112811 / 100000) := by
  exact
    packedTile65536 2828486912 2828617984 14 5989 53183 31 _ _ (2176299 / 100000) (1088151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2828617984 :
    ThetaLowerSegment 2828617984 2828749056 (282856224112811 / 100000)
      (282869205766171 / 100000) := by
  exact
    packedTile65536 2828617984 2828749056 14 5965 53184 31 _ _ (136019 / 6250) (2176307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2828749056 :
    ThetaLowerSegment 2828749056 2828880128 (282869205766171 / 100000) (8840068629831 / 3125) := by
  exact
    packedTile65536 2828749056 2828880128 14 5969 53185 31 _ _ (2176309 / 100000) (272039 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2828880128 :
    ThetaLowerSegment 2828880128 2829011200 (8840068629831 / 3125) (282895317145669 / 100000) := by
  exact
    packedTile65536 2828880128 2829011200 14 6029 53187 31 _ _ (2176313 / 100000) (544079 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2829011200 :
    ThetaLowerSegment 2829011200 2829142272 (282895317145669 / 100000)
      (282908525219611 / 100000) := by
  exact
    packedTile65536 2829011200 2829142272 14 6069 53188 31 _ _ (1088159 / 50000) (2176321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2829142272 :
    ThetaLowerSegment 2829142272 2829273344 (282908525219611 / 100000) (11316862194377 / 4000) := by
  exact
    packedTile65536 2829142272 2829273344 14 5987 53189 31 _ _ (1088161 / 50000) (87053 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2829273344 :
    ThetaLowerSegment 2829273344 2829404416 (11316862194377 / 4000) (14146735537807 / 5000) := by
  exact
    packedTile65536 2829273344 2829404416 14 6045 53190 31 _ _ (2176327 / 100000) (217633 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2829404416 :
    ThetaLowerSegment 2829404416 2829535488 (14146735537807 / 5000) (70737005300663 / 25000) := by
  exact
    packedTile65536 2829404416 2829535488 14 6116 53192 31 _ _ (544083 / 25000) (435267 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2829535488 :
    ThetaLowerSegment 2829535488 2829666560 (70737005300663 / 25000) (70740243144547 / 25000) := by
  exact
    packedTile65536 2829535488 2829666560 14 5951 53193 31 _ _ (136021 / 6250) (2176339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2829666560 :
    ThetaLowerSegment 2829666560 2829797632 (70740243144547 / 25000)
      (282974159028307 / 100000) := by
  exact
    packedTile65536 2829666560 2829797632 14 6059 53194 31 _ _ (2176341 / 100000) (272043 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2829797632 :
    ThetaLowerSegment 2829797632 2829928704 (282974159028307 / 100000)
      (56597462137437 / 20000) := by
  exact
    packedTile65536 2829797632 2829928704 14 6043 53195 31 _ _ (1088173 / 50000) (2176349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2829928704 :
    ThetaLowerSegment 2829928704 2830059776 (56597462137437 / 20000) (56600103791067 / 20000) := by
  exact
    packedTile65536 2829928704 2830059776 14 6069 53197 31 _ _ (43527 / 2000) (2176353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2830059776 :
    ThetaLowerSegment 2830059776 2830190848 (56600103791067 / 20000) (566027254283 / 200) := by
  exact
    packedTile65536 2830059776 2830190848 14 6023 53198 31 _ _ (435271 / 20000) (1088179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2830190848 :
    ThetaLowerSegment 2830190848 2830321920 (566027254283 / 200) (70756710498337 / 25000) := by
  exact
    packedTile65536 2830190848 2830321920 14 6072 53199 31 _ _ (2176359 / 100000) (1088181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2830321920 :
    ThetaLowerSegment 2830321920 2830452992 (70756710498337 / 25000) (70759948927969 / 25000) := by
  exact
    packedTile65536 2830321920 2830452992 14 5952 53200 31 _ _ (544091 / 25000) (2176367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2830452992 :
    ThetaLowerSegment 2830452992 2830584064 (70759948927969 / 25000)
      (283052956215219 / 100000) := by
  exact
    packedTile65536 2830452992 2830584064 14 6047 53202 31 _ _ (2176369 / 100000) (544093 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2830584064 :
    ThetaLowerSegment 2830584064 2830715136 (283052956215219 / 100000)
      (141533006138423 / 50000) := by
  exact
    packedTile65536 2830584064 2830715136 14 5999 53203 31 _ _ (2176373 / 100000) (272047 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2830715136 :
    ThetaLowerSegment 2830715136 2830846208 (141533006138423 / 50000) (28307902266453 / 10000) := by
  exact
    packedTile65536 2830715136 2830846208 14 5978 53204 31 _ _ (1088189 / 50000) (2176381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2830846208 :
    ThetaLowerSegment 2830846208 2830977280 (28307902266453 / 10000)
      (283092248544021 / 100000) := by
  exact
    packedTile65536 2830846208 2830977280 14 6077 53205 31 _ _ (2176383 / 100000) (1088193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2830977280 :
    ThetaLowerSegment 2830977280 2831108352 (283092248544021 / 100000)
      (141552613169851 / 50000) := by
  exact
    packedTile65536 2830977280 2831108352 14 5963 53206 31 _ _ (2176387 / 100000) (217639 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2831108352 :
    ThetaLowerSegment 2831108352 2831239424 (141552613169851 / 50000)
      (141559143434047 / 50000) := by
  exact
    packedTile65536 2831108352 2831239424 14 6001 53208 31 _ _ (272049 / 12500) (435279 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2831239424 :
    ThetaLowerSegment 2831239424 2831370496 (141559143434047 / 50000) (70782848282707 / 25000) := by
  exact
    packedTile65536 2831239424 2831370496 14 6022 53209 31 _ _ (2176397 / 100000) (5441 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2831370496 :
    ThetaLowerSegment 2831370496 2831501568 (70782848282707 / 25000)
      (283144527710863 / 100000) := by
  exact
    packedTile65536 2831370496 2831501568 14 6035 53210 31 _ _ (2176401 / 100000) (544101 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2831501568 :
    ThetaLowerSegment 2831501568 2831632640 (283144527710863 / 100000)
      (283157466444533 / 100000) := by
  exact
    packedTile65536 2831501568 2831632640 14 5945 53211 31 _ _ (1088203 / 50000) (2176409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2831632640 :
    ThetaLowerSegment 2831632640 2831763712 (283157466444533 / 100000)
      (283170653312723 / 100000) := by
  exact
    packedTile65536 2831632640 2831763712 14 6059 53213 31 _ _ (217641 / 10000) (2176413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2831763712 :
    ThetaLowerSegment 2831763712 2831894784 (283170653312723 / 100000)
      (70795940465067 / 25000) := by
  exact
    packedTile65536 2831763712 2831894784 14 6023 53214 31 _ _ (435283 / 20000) (1088209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2831894784 :
    ThetaLowerSegment 2831894784 2832025856 (70795940465067 / 25000) (17699798145163 / 6250) := by
  exact
    packedTile65536 2831894784 2832025856 14 5977 53215 31 _ _ (108821 / 5000) (2176423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2832025856 :
    ThetaLowerSegment 2832025856 2832156928 (17699798145163 / 6250) (17700615936481 / 6250) := by
  exact
    packedTile65536 2832025856 2832156928 14 6012 53216 31 _ _ (272053 / 12500) (2176427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2832156928 :
    ThetaLowerSegment 2832156928 2832288000 (17700615936481 / 6250) (141611437190987 / 50000) := by
  exact
    packedTile65536 2832156928 2832288000 14 5982 53218 31 _ _ (2176429 / 100000) (136027 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2832288000 :
    ThetaLowerSegment 2832288000 2832419072 (141611437190987 / 50000) (14161792187609 / 5000) := by
  exact
    packedTile65536 2832288000 2832419072 14 5959 53219 31 _ _ (1088217 / 50000) (2176437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2832419072 :
    ThetaLowerSegment 2832419072 2832550144 (14161792187609 / 5000) (141624534982953 / 50000) := by
  exact
    packedTile65536 2832419072 2832550144 14 6077 53220 31 _ _ (1088219 / 50000) (2176441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2832550144 :
    ThetaLowerSegment 2832550144 2832681216 (141624534982953 / 50000)
      (141631090429269 / 50000) := by
  exact
    packedTile65536 2832550144 2832681216 14 6024 53221 31 _ _ (2176443 / 100000) (1088223 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2832681216 :
    ThetaLowerSegment 2832681216 2832812288 (141631090429269 / 50000) (56655022226033 / 20000) := by
  exact
    packedTile65536 2832681216 2832812288 14 5941 53222 31 _ _ (2176447 / 100000) (43529 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2832812288 :
    ThetaLowerSegment 2832812288 2832943360 (56655022226033 / 20000)
      (283288143724741 / 100000) := by
  exact
    packedTile65536 2832812288 2832943360 14 5988 53224 31 _ _ (544113 / 25000) (435291 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2832943360 :
    ThetaLowerSegment 2832943360 2833074432 (283288143724741 / 100000) (14165065238011 / 5000) := by
  exact
    packedTile65536 2832943360 2833074432 14 6047 53225 31 _ _ (2176457 / 100000) (108823 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2833074432 :
    ThetaLowerSegment 2833074432 2833205504 (14165065238011 / 5000) (283314552878327 / 100000) := by
  exact
    packedTile65536 2833074432 2833205504 14 6087 53226 31 _ _ (2176461 / 100000) (136029 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2833205504 :
    ThetaLowerSegment 2833205504 2833336576 (283314552878327 / 100000)
      (283327676968307 / 100000) := by
  exact
    packedTile65536 2833205504 2833336576 14 6030 53227 31 _ _ (1088233 / 50000) (2176469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2833336576 :
    ThetaLowerSegment 2833336576 2833467648 (283327676968307 / 100000)
      (70835183404459 / 25000) := by
  exact
    packedTile65536 2833336576 2833467648 14 5999 53229 31 _ _ (2176471 / 100000) (1088237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2833467648 :
    ThetaLowerSegment 2833467648 2833598720 (70835183404459 / 25000)
      (283353890409211 / 100000) := by
  exact
    packedTile65536 2833467648 2833598720 14 6045 53230 31 _ _ (87059 / 4000) (1088239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2833598720 :
    ThetaLowerSegment 2833598720 2833729792 (283353890409211 / 100000)
      (283366820876891 / 100000) := by
  exact
    packedTile65536 2833598720 2833729792 14 5941 53231 31 _ _ (13603 / 625) (2176483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2833729792 :
    ThetaLowerSegment 2833729792 2833860864 (283366820876891 / 100000)
      (283379908075183 / 100000) := by
  exact
    packedTile65536 2833729792 2833860864 14 6013 53232 31 _ _ (544121 / 25000) (2176487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2833860864 :
    ThetaLowerSegment 2833860864 2833991936 (283379908075183 / 100000)
      (283393032303853 / 100000) := by
  exact
    packedTile65536 2833860864 2833991936 14 6030 53234 31 _ _ (2176489 / 100000) (544123 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2833991936 :
    ThetaLowerSegment 2833991936 2834123008 (283393032303853 / 100000)
      (283406226210481 / 100000) := by
  exact
    packedTile65536 2833991936 2834123008 14 6062 53235 31 _ _ (1088247 / 50000) (2176497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2834123008 :
    ThetaLowerSegment 2834123008 2834254080 (283406226210481 / 100000)
      (283419376611397 / 100000) := by
  exact
    packedTile65536 2834123008 2834254080 14 6042 53236 31 _ _ (1088249 / 50000) (2176501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2834254080 :
    ThetaLowerSegment 2834254080 2834385152 (283419376611397 / 100000)
      (283432561866571 / 100000) := by
  exact
    packedTile65536 2834254080 2834385152 14 6058 53237 31 _ _ (2176503 / 100000) (1088253 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2834385152 :
    ThetaLowerSegment 2834385152 2834516224 (283432561866571 / 100000)
      (56689110253263 / 20000) := by
  exact
    packedTile65536 2834385152 2834516224 14 5968 53238 31 _ _ (544127 / 25000) (2176511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2834516224 :
    ThetaLowerSegment 2834516224 2834647296 (56689110253263 / 20000)
      (283458629926923 / 100000) := by
  exact
    packedTile65536 2834516224 2834647296 14 6009 53240 31 _ _ (68016 / 3125) (435303 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2834647296 :
    ThetaLowerSegment 2834647296 2834778368 (283458629926923 / 100000)
      (283471823972977 / 100000) := by
  exact
    packedTile65536 2834647296 2834778368 14 6062 53241 31 _ _ (2176517 / 100000) (54413 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2834778368 :
    ThetaLowerSegment 2834778368 2834909440 (283471823972977 / 100000)
      (141742473109043 / 50000) := by
  exact
    packedTile65536 2834778368 2834909440 14 6029 53242 31 _ _ (2176521 / 100000) (544131 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2834909440 :
    ThetaLowerSegment 2834909440 2835040512 (141742473109043 / 50000)
      (141749026628829 / 50000) := by
  exact
    packedTile65536 2834909440 2835040512 14 6022 53243 31 _ _ (1088263 / 50000) (2176529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2835040512 :
    ThetaLowerSegment 2835040512 2835171584 (141749026628829 / 50000)
      (141755534456519 / 50000) := by
  exact
    packedTile65536 2835040512 2835171584 14 5980 53245 31 _ _ (2176531 / 100000) (1088267 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2835171584 :
    ThetaLowerSegment 2835171584 2835302656 (141755534456519 / 50000)
      (141762059708449 / 50000) := by
  exact
    packedTile65536 2835171584 2835302656 14 5996 53246 31 _ _ (435307 / 20000) (1088269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2835302656 :
    ThetaLowerSegment 2835302656 2835433728 (141762059708449 / 50000)
      (141768645918489 / 50000) := by
  exact
    packedTile65536 2835302656 2835433728 14 6052 53247 31 _ _ (108827 / 5000) (2176543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2835433728 :
    ThetaLowerSegment 2835433728 2835564800 (141768645918489 / 50000)
      (283550470816953 / 100000) := by
  exact
    packedTile65536 2835433728 2835564800 14 6055 53248 31 _ _ (435309 / 20000) (544137 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2835564800 :
    ThetaLowerSegment 2835564800 2835695872 (283550470816953 / 100000)
      (70890842805719 / 25000) := by
  exact
    packedTile65536 2835564800 2835695872 14 5927 53250 31 _ _ (2176549 / 100000) (272069 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2835695872 :
    ThetaLowerSegment 2835695872 2835826944 (70890842805719 / 25000) (35447061980437 / 12500) := by
  exact
    packedTile65536 2835695872 2835826944 14 6030 53251 31 _ _ (1088277 / 50000) (2176557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2835826944 :
    ThetaLowerSegment 2835826944 2835958016 (35447061980437 / 12500) (70897370297131 / 25000) := by
  exact
    packedTile65536 2835826944 2835958016 14 5966 53252 31 _ _ (1088279 / 50000) (2176561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2835958016 :
    ThetaLowerSegment 2835958016 2836089088 (70897370297131 / 25000) (141801333403589 / 50000) := by
  exact
    packedTile65536 2835958016 2836089088 14 6058 53253 31 _ _ (2176563 / 100000) (1088283 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2836089088 :
    ThetaLowerSegment 2836089088 2836220160 (141801333403589 / 50000)
      (141807887049837 / 50000) := by
  exact
    packedTile65536 2836089088 2836220160 14 6022 53254 31 _ _ (272071 / 12500) (2176571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2836220160 :
    ThetaLowerSegment 2836220160 2836351232 (141807887049837 / 50000) (28362888359283 / 10000) := by
  exact
    packedTile65536 2836220160 2836351232 14 6023 53256 31 _ _ (544143 / 25000) (87063 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2836351232 :
    ThetaLowerSegment 2836351232 2836482304 (28362888359283 / 10000) (141821032471571 / 50000) := by
  exact
    packedTile65536 2836351232 2836482304 14 6056 53257 31 _ _ (2176577 / 100000) (108829 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2836482304 :
    ThetaLowerSegment 2836482304 2836613376 (141821032471571 / 50000) (70913831714317 / 25000) := by
  exact
    packedTile65536 2836482304 2836613376 14 6093 53258 31 _ _ (1088291 / 50000) (435317 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2836613376 :
    ThetaLowerSegment 2836613376 2836744448 (70913831714317 / 25000) (28366837984351 / 10000) := by
  exact
    packedTile65536 2836613376 2836744448 14 5997 53259 31 _ _ (1088293 / 50000) (2176589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2836744448 :
    ThetaLowerSegment 2836744448 2836875520 (28366837984351 / 10000)
      (283681367562007 / 100000) := by
  exact
    packedTile65536 2836744448 2836875520 14 5967 53261 31 _ _ (2176591 / 100000) (1088297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2836875520 :
    ThetaLowerSegment 2836875520 2837006592 (283681367562007 / 100000) (17730904280457 / 6250) := by
  exact
    packedTile65536 2836875520 2837006592 14 6019 53262 31 _ _ (435319 / 20000) (1088299 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2837006592 :
    ThetaLowerSegment 2837006592 2837137664 (17730904280457 / 6250) (8865865014041 / 3125) := by
  exact
    packedTile65536 2837006592 2837137664 14 6070 53263 31 _ _ (10883 / 500) (2176603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2837137664 :
    ThetaLowerSegment 2837137664 2837268736 (8865865014041 / 3125) (35465099039729 / 12500) := by
  exact
    packedTile65536 2837137664 2837268736 14 6024 53264 31 _ _ (435321 / 20000) (68019 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2837268736 :
    ThetaLowerSegment 2837268736 2837399808 (35465099039729 / 12500) (35466714083607 / 12500) := by
  exact
    packedTile65536 2837268736 2837399808 14 5936 53266 31 _ _ (2176609 / 100000) (544153 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2837399808 :
    ThetaLowerSegment 2837399808 2837530880 (35466714083607 / 12500) (17734180346049 / 6250) := by
  exact
    packedTile65536 2837399808 2837530880 14 6052 53267 31 _ _ (1088307 / 50000) (2176617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2837530880 :
    ThetaLowerSegment 2837530880 2837661952 (17734180346049 / 6250) (70940001549029 / 25000) := by
  exact
    packedTile65536 2837530880 2837661952 14 6028 53268 31 _ _ (2176619 / 100000) (1088311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2837661952 :
    ThetaLowerSegment 2837661952 2837793024 (70940001549029 / 25000)
      (283773142115921 / 100000) := by
  exact
    packedTile65536 2837661952 2837793024 14 6035 53269 31 _ _ (2176623 / 100000) (1088313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2837793024 :
    ThetaLowerSegment 2837793024 2837924096 (283773142115921 / 100000)
      (283786323775089 / 100000) := by
  exact
    packedTile65536 2837793024 2837924096 14 6056 53270 31 _ _ (544157 / 25000) (2176631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2837924096 :
    ThetaLowerSegment 2837924096 2838055168 (283786323775089 / 100000)
      (283799287795281 / 100000) := by
  exact
    packedTile65536 2837924096 2838055168 14 5956 53272 31 _ _ (272079 / 12500) (435327 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2838055168 :
    ThetaLowerSegment 2838055168 2838186240 (283799287795281 / 100000)
      (283812391150021 / 100000) := by
  exact
    packedTile65536 2838055168 2838186240 14 6020 53273 31 _ _ (2176637 / 100000) (13604 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2838186240 :
    ThetaLowerSegment 2838186240 2838317312 (283812391150021 / 100000)
      (283825472768441 / 100000) := by
  exact
    packedTile65536 2838186240 2838317312 14 6010 53274 31 _ _ (1088321 / 50000) (435329 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2838317312 :
    ThetaLowerSegment 2838317312 2838448384 (283825472768441 / 100000)
      (283838523937857 / 100000) := by
  exact
    packedTile65536 2838317312 2838448384 14 5996 53275 31 _ _ (1088323 / 50000) (2176649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2838448384 :
    ThetaLowerSegment 2838448384 2838579456 (283838523937857 / 100000) (17740740995327 / 6250) := by
  exact
    packedTile65536 2838448384 2838579456 14 6125 53277 31 _ _ (2176651 / 100000) (1088327 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2838579456 :
    ThetaLowerSegment 2838579456 2838710528 (17740740995327 / 6250) (141932455750961 / 50000) := by
  exact
    packedTile65536 2838579456 2838710528 14 5998 53278 31 _ _ (435331 / 20000) (1088329 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2838710528 :
    ThetaLowerSegment 2838710528 2838841600 (141932455750961 / 50000)
      (141939034705811 / 50000) := by
  exact
    packedTile65536 2838710528 2838841600 14 6045 53279 31 _ _ (108833 / 5000) (2176663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2838841600 :
    ThetaLowerSegment 2838841600 2838972672 (141939034705811 / 50000) (70972772555413 / 25000) := by
  exact
    packedTile65536 2838841600 2838972672 14 5982 53280 31 _ _ (435333 / 20000) (544167 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2838972672 :
    ThetaLowerSegment 2838972672 2839103744 (70972772555413 / 25000) (14195210994453 / 5000) := by
  exact
    packedTile65536 2838972672 2839103744 14 6032 53282 31 _ _ (2176669 / 100000) (68021 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2839103744 :
    ThetaLowerSegment 2839103744 2839234816 (14195210994453 / 5000) (141958658468259 / 50000) := by
  exact
    packedTile65536 2839103744 2839234816 14 6017 53283 31 _ _ (1088337 / 50000) (2176677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2839234816 :
    ThetaLowerSegment 2839234816 2839365888 (141958658468259 / 50000) (56786072354753 / 20000) := by
  exact
    packedTile65536 2839234816 2839365888 14 5993 53284 31 _ _ (2176679 / 100000) (1088341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2839365888 :
    ThetaLowerSegment 2839365888 2839496960 (56786072354753 / 20000)
      (283943430578497 / 100000) := by
  exact
    packedTile65536 2839365888 2839496960 14 6004 53285 31 _ _ (2176683 / 100000) (1088343 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2839496960 :
    ThetaLowerSegment 2839496960 2839628032 (283943430578497 / 100000)
      (283956484176433 / 100000) := by
  exact
    packedTile65536 2839496960 2839628032 14 5997 53286 31 _ _ (136043 / 6250) (2176691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2839628032 :
    ThetaLowerSegment 2839628032 2839759104 (283956484176433 / 100000)
      (283969718463793 / 100000) := by
  exact
    packedTile65536 2839628032 2839759104 14 6080 53288 31 _ _ (544173 / 25000) (435339 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2839759104 :
    ThetaLowerSegment 2839759104 2839890176 (283969718463793 / 100000)
      (141991442651973 / 50000) := by
  exact
    packedTile65536 2839759104 2839890176 14 6049 53289 31 _ _ (2176697 / 100000) (21767 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2839890176 :
    ThetaLowerSegment 2839890176 2840021248 (141991442651973 / 50000) (1135983364137 / 400) := by
  exact
    packedTile65536 2839890176 2840021248 14 5952 53290 31 _ _ (1088351 / 50000) (435341 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2840021248 :
    ThetaLowerSegment 2840021248 2840152320 (1135983364137 / 400) (1420044234263 / 500) := by
  exact
    packedTile65536 2840021248 2840152320 14 5975 53291 31 _ _ (1088353 / 50000) (2176709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2840152320 :
    ThetaLowerSegment 2840152320 2840283392 (1420044234263 / 500) (17751381166823 / 6250) := by
  exact
    packedTile65536 2840152320 2840283392 14 6088 53293 31 _ _ (2176711 / 100000) (1088357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2840283392 :
    ThetaLowerSegment 2840283392 2840414464 (17751381166823 / 6250) (142017633897459 / 50000) := by
  exact
    packedTile65536 2840283392 2840414464 14 6050 53294 31 _ _ (435343 / 20000) (1088359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2840414464 :
    ThetaLowerSegment 2840414464 2840545536 (142017633897459 / 50000)
      (142024179294499 / 50000) := by
  exact
    packedTile65536 2840414464 2840545536 14 6014 53295 31 _ _ (27209 / 1250) (2176723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2840545536 :
    ThetaLowerSegment 2840545536 2840676608 (142024179294499 / 50000)
      (142030687702249 / 50000) := by
  exact
    packedTile65536 2840545536 2840676608 14 5980 53296 31 _ _ (87069 / 4000) (272091 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2840676608 :
    ThetaLowerSegment 2840676608 2840807680 (142030687702249 / 50000) (56814901522111 / 20000) := by
  exact
    packedTile65536 2840676608 2840807680 14 6033 53297 31 _ _ (2176729 / 100000) (544183 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2840807680 :
    ThetaLowerSegment 2840807680 2840938752 (56814901522111 / 20000)
      (284087811808763 / 100000) := by
  exact
    packedTile65536 2840807680 2840938752 14 6112 53299 31 _ _ (1088367 / 50000) (2176737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2840938752 :
    ThetaLowerSegment 2840938752 2841069824 (284087811808763 / 100000)
      (284100907070587 / 100000) := by
  exact
    packedTile65536 2840938752 2841069824 14 6016 53300 31 _ _ (2176739 / 100000) (1088371 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2841069824 :
    ThetaLowerSegment 2841069824 2841200896 (284100907070587 / 100000)
      (56822769996893 / 20000) := by
  exact
    packedTile65536 2841069824 2841200896 14 5946 53301 31 _ _ (2176743 / 100000) (1088373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2841200896 :
    ThetaLowerSegment 2841200896 2841331968 (56822769996893 / 20000)
      (284126875644497 / 100000) := by
  exact
    packedTile65536 2841200896 2841331968 14 5984 53302 31 _ _ (544187 / 25000) (2176751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2841331968 :
    ThetaLowerSegment 2841331968 2841463040 (284126875644497 / 100000)
      (284140018873073 / 100000) := by
  exact
    packedTile65536 2841331968 2841463040 14 6038 53304 31 _ _ (136047 / 6250) (435351 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2841463040 :
    ThetaLowerSegment 2841463040 2841594112 (284140018873073 / 100000)
      (142076488553747 / 50000) := by
  exact
    packedTile65536 2841463040 2841594112 14 5953 53305 31 _ _ (2176757 / 100000) (54419 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2841594112 :
    ThetaLowerSegment 2841594112 2841725184 (142076488553747 / 50000) (35520745186603 / 12500) := by
  exact
    packedTile65536 2841594112 2841725184 14 5965 53306 31 _ _ (1088381 / 50000) (435353 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2841725184 :
    ThetaLowerSegment 2841725184 2841856256 (35520745186603 / 12500) (142089525193391 / 50000) := by
  exact
    packedTile65536 2841725184 2841856256 14 6013 53307 31 _ _ (1088383 / 50000) (2176769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2841856256 :
    ThetaLowerSegment 2841856256 2841987328 (142089525193391 / 50000) (14209616216817 / 5000) := by
  exact
    packedTile65536 2841856256 2841987328 14 6098 53309 31 _ _ (2176771 / 100000) (1088387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2841987328 :
    ThetaLowerSegment 2841987328 2842118400 (14209616216817 / 5000) (28420546770379 / 10000) := by
  exact
    packedTile65536 2841987328 2842118400 14 6038 53310 31 _ _ (87071 / 4000) (1088389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2842118400 :
    ThetaLowerSegment 2842118400 2842249472 (28420546770379 / 10000) (28421859368719 / 10000) := by
  exact
    packedTile65536 2842118400 2842249472 14 6030 53311 31 _ _ (108839 / 5000) (2176783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2842249472 :
    ThetaLowerSegment 2842249472 2842380544 (28421859368719 / 10000) (56846339151221 / 20000) := by
  exact
    packedTile65536 2842249472 2842380544 14 6019 53312 31 _ _ (435357 / 20000) (544197 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2842380544 :
    ThetaLowerSegment 2842380544 2842511616 (56846339151221 / 20000)
      (284244730368637 / 100000) := by
  exact
    packedTile65536 2842380544 2842511616 14 5988 53313 31 _ _ (2176789 / 100000) (272099 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2842511616 :
    ThetaLowerSegment 2842511616 2842642688 (284244730368637 / 100000)
      (284257867320427 / 100000) := by
  exact
    packedTile65536 2842511616 2842642688 14 6035 53315 31 _ _ (1088397 / 50000) (2176797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2842642688 :
    ThetaLowerSegment 2842642688 2842773760 (284257867320427 / 100000)
      (284270928108427 / 100000) := by
  exact
    packedTile65536 2842642688 2842773760 14 6000 53316 31 _ _ (1088399 / 50000) (2176801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2842773760 :
    ThetaLowerSegment 2842773760 2842904832 (284270928108427 / 100000)
      (284284028108881 / 100000) := by
  exact
    packedTile65536 2842773760 2842904832 14 6018 53317 31 _ _ (2176803 / 100000) (1088403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2842904832 :
    ThetaLowerSegment 2842904832 2843035904 (284284028108881 / 100000)
      (284297115078577 / 100000) := by
  exact
    packedTile65536 2842904832 2843035904 14 6012 53318 31 _ _ (272101 / 12500) (2176811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2843035904 :
    ThetaLowerSegment 2843035904 2843166976 (284297115078577 / 100000)
      (284310258669433 / 100000) := by
  exact
    packedTile65536 2843035904 2843166976 14 6038 53320 31 _ _ (544203 / 25000) (435363 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2843166976 :
    ThetaLowerSegment 2843166976 2843298048 (284310258669433 / 100000)
      (142161612984151 / 50000) := by
  exact
    packedTile65536 2843166976 2843298048 14 5957 53321 31 _ _ (2176817 / 100000) (108841 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2843298048 :
    ThetaLowerSegment 2843298048 2843429120 (142161612984151 / 50000)
      (142168173925659 / 50000) := by
  exact
    packedTile65536 2843298048 2843429120 14 6028 53322 31 _ _ (1088411 / 50000) (87073 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2843429120 :
    ThetaLowerSegment 2843429120 2843560192 (142168173925659 / 50000) (71087393017317 / 25000) := by
  exact
    packedTile65536 2843429120 2843560192 14 6075 53323 31 _ _ (1088413 / 50000) (2176829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2843560192 :
    ThetaLowerSegment 2843560192 2843691264 (71087393017317 / 25000)
      (284362696183367 / 100000) := by
  exact
    packedTile65536 2843560192 2843691264 14 6029 53325 31 _ _ (2176831 / 100000) (1088417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2843691264 :
    ThetaLowerSegment 2843691264 2843822336 (284362696183367 / 100000)
      (142187823087391 / 50000) := by
  exact
    packedTile65536 2843691264 2843822336 14 5949 53326 31 _ _ (435367 / 20000) (1088419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2843822336 :
    ThetaLowerSegment 2843822336 2843953408 (142187823087391 / 50000)
      (142194425443111 / 50000) := by
  exact
    packedTile65536 2843822336 2843953408 14 6066 53327 31 _ _ (54421 / 2500) (2176843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2843953408 :
    ThetaLowerSegment 2843953408 2844084480 (142194425443111 / 50000)
      (284401931547827 / 100000) := by
  exact
    packedTile65536 2843953408 2844084480 14 6009 53328 31 _ _ (435369 / 20000) (136053 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2844084480 :
    ThetaLowerSegment 2844084480 2844215552 (284401931547827 / 100000) (14220751482413 / 5000) := by
  exact
    packedTile65536 2844084480 2844215552 14 6017 53329 31 _ _ (2176849 / 100000) (544213 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2844215552 :
    ThetaLowerSegment 2844215552 2844346624 (14220751482413 / 5000) (142214013821747 / 50000) := by
  exact
    packedTile65536 2844215552 2844346624 14 5971 53331 31 _ _ (1088427 / 50000) (2176857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2844346624 :
    ThetaLowerSegment 2844346624 2844477696 (142214013821747 / 50000) (28444100607089 / 10000) := by
  exact
    packedTile65536 2844346624 2844477696 14 5962 53332 31 _ _ (1088429 / 50000) (2176861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2844477696 :
    ThetaLowerSegment 2844477696 2844608768 (28444100607089 / 10000)
      (284454052010849 / 100000) := by
  exact
    packedTile65536 2844477696 2844608768 14 5993 53333 31 _ _ (2176863 / 100000) (1088433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2844608768 :
    ThetaLowerSegment 2844608768 2844739840 (284454052010849 / 100000)
      (284467069681489 / 100000) := by
  exact
    packedTile65536 2844608768 2844739840 14 5980 53334 31 _ _ (544217 / 25000) (2176871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2844739840 :
    ThetaLowerSegment 2844739840 2844870912 (284467069681489 / 100000)
      (56896029665693 / 20000) := by
  exact
    packedTile65536 2844739840 2844870912 14 6008 53336 31 _ _ (272109 / 12500) (3483 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2844870912 :
    ThetaLowerSegment 2844870912 2845001984 (56896029665693 / 20000) (142246688604997 / 50000) := by
  exact
    packedTile65536 2844870912 2845001984 14 6077 53337 31 _ _ (2176877 / 100000) (27211 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2845001984 :
    ThetaLowerSegment 2845001984 2845133056 (142246688604997 / 50000)
      (284506414550303 / 100000) := by
  exact
    packedTile65536 2845001984 2845133056 14 5989 53338 31 _ _ (2176881 / 100000) (544221 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2845133056 :
    ThetaLowerSegment 2845133056 2845264128 (284506414550303 / 100000)
      (284519562941743 / 100000) := by
  exact
    packedTile65536 2845133056 2845264128 14 6040 53339 31 _ _ (1088443 / 50000) (2176889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2845264128 :
    ThetaLowerSegment 2845264128 2845395200 (284519562941743 / 100000)
      (284532872453317 / 100000) := by
  exact
    packedTile65536 2845264128 2845395200 14 6114 53341 31 _ _ (2176891 / 100000) (1088447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2845395200 :
    ThetaLowerSegment 2845395200 2845526272 (284532872453317 / 100000)
      (142272913577731 / 50000) := by
  exact
    packedTile65536 2845395200 2845526272 14 5951 53342 31 _ _ (435379 / 20000) (1088449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2845526272 :
    ThetaLowerSegment 2845526272 2845657344 (142272913577731 / 50000)
      (142279524823031 / 50000) := by
  exact
    packedTile65536 2845526272 2845657344 14 6074 53343 31 _ _ (21769 / 1000) (2176903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2845657344 :
    ThetaLowerSegment 2845657344 2845788416 (142279524823031 / 50000)
      (142286108869179 / 50000) := by
  exact
    packedTile65536 2845657344 2845788416 14 6049 53344 31 _ _ (272113 / 12500) (2176907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2845788416 :
    ThetaLowerSegment 2845788416 2845919488 (142286108869179 / 50000)
      (142292717964903 / 50000) := by
  exact
    packedTile65536 2845788416 2845919488 14 6072 53345 31 _ _ (2176909 / 100000) (136057 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2845919488 :
    ThetaLowerSegment 2845919488 2846050560 (142292717964903 / 50000) (17787416020533 / 6250) := by
  exact
    packedTile65536 2845919488 2846050560 14 6073 53347 31 _ _ (1088457 / 50000) (2176917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2846050560 :
    ThetaLowerSegment 2846050560 2846181632 (17787416020533 / 6250) (142305838237543 / 50000) := by
  exact
    packedTile65536 2846050560 2846181632 14 5981 53348 31 _ _ (1088459 / 50000) (2176921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2846181632 :
    ThetaLowerSegment 2846181632 2846312704 (142305838237543 / 50000) (28462484250539 / 10000) := by
  exact
    packedTile65536 2846181632 2846312704 14 6048 53349 31 _ _ (2176923 / 100000) (1088463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2846312704 :
    ThetaLowerSegment 2846312704 2846443776 (28462484250539 / 10000) (142319030406103 / 50000) := by
  exact
    packedTile65536 2846312704 2846443776 14 6072 53350 31 _ _ (68029 / 3125) (2176931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2846443776 :
    ThetaLowerSegment 2846443776 2846574848 (142319030406103 / 50000)
      (142325559025171 / 50000) := by
  exact
    packedTile65536 2846443776 2846574848 14 5998 53352 31 _ _ (544233 / 25000) (435387 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2846574848 :
    ThetaLowerSegment 2846574848 2846705920 (142325559025171 / 50000) (56932874683947 / 20000) := by
  exact
    packedTile65536 2846574848 2846705920 14 6089 53353 31 _ _ (2176937 / 100000) (108847 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2846705920 :
    ThetaLowerSegment 2846705920 2846836992 (56932874683947 / 20000) (35584693805451 / 12500) := by
  exact
    packedTile65536 2846705920 2846836992 14 6053 53354 31 _ _ (2176941 / 100000) (136059 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2846836992 :
    ThetaLowerSegment 2846836992 2846968064 (35584693805451 / 12500) (71172660649213 / 25000) := by
  exact
    packedTile65536 2846836992 2846968064 14 6014 53355 31 _ _ (1088473 / 50000) (2176949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2846968064 :
    ThetaLowerSegment 2846968064 2847099136 (71172660649213 / 25000) (28470365640993 / 10000) := by
  exact
    packedTile65536 2846968064 2847099136 14 5978 53356 31 _ _ (2176951 / 100000) (1088477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2847099136 :
    ThetaLowerSegment 2847099136 2847230208 (28470365640993 / 10000) (28471674426339 / 10000) := by
  exact
    packedTile65536 2847099136 2847230208 14 6012 53358 31 _ _ (435391 / 20000) (1088479 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2847230208 :
    ThetaLowerSegment 2847230208 2847361280 (28471674426339 / 10000) (28472979949251 / 10000) := by
  exact
    packedTile65536 2847230208 2847361280 14 5997 53359 31 _ _ (13606 / 625) (2176963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2847361280 :
    ThetaLowerSegment 2847361280 2847492352 (28472979949251 / 10000) (142371418664953 / 50000) := by
  exact
    packedTile65536 2847361280 2847492352 14 5989 53360 31 _ _ (544241 / 25000) (2176967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2847492352 :
    ThetaLowerSegment 2847492352 2847623424 (142371418664953 / 50000)
      (142377958279829 / 50000) := by
  exact
    packedTile65536 2847492352 2847623424 14 6008 53361 31 _ _ (2176969 / 100000) (544243 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2847623424 :
    ThetaLowerSegment 2847623424 2847754496 (142377958279829 / 50000)
      (142384569749867 / 50000) := by
  exact
    packedTile65536 2847623424 2847754496 14 6074 53363 31 _ _ (1088487 / 50000) (2176977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2847754496 :
    ThetaLowerSegment 2847754496 2847885568 (142384569749867 / 50000) (8899444677139 / 3125) := by
  exact
    packedTile65536 2847754496 2847885568 14 6013 53364 31 _ _ (1088489 / 50000) (2176981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2847885568 :
    ThetaLowerSegment 2847885568 2848016640 (8899444677139 / 3125) (56959079647723 / 20000) := by
  exact
    packedTile65536 2847885568 2848016640 14 6049 53365 31 _ _ (2176983 / 100000) (1088493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2848016640 :
    ThetaLowerSegment 2848016640 2848147712 (56959079647723 / 20000) (56961670262253 / 20000) := by
  exact
    packedTile65536 2848016640 2848147712 14 5950 53366 31 _ _ (2176987 / 100000) (217699 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2848147712 :
    ThetaLowerSegment 2848147712 2848278784 (56961670262253 / 20000)
      (284821419794241 / 100000) := by
  exact
    packedTile65536 2848147712 2848278784 14 6003 53368 31 _ _ (68031 / 3125) (435399 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2848278784 :
    ThetaLowerSegment 2848278784 2848409856 (284821419794241 / 100000) (14241720496767 / 5000) := by
  exact
    packedTile65536 2848278784 2848409856 14 5967 53369 31 _ _ (2176997 / 100000) (2177 / 100)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2848409856 :
    ThetaLowerSegment 2848409856 2848540928 (14241720496767 / 5000) (142423838289717 / 50000) := by
  exact
    packedTile65536 2848409856 2848540928 14 6094 53370 31 _ _ (2177001 / 100000) (544251 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2848540928 :
    ThetaLowerSegment 2848540928 2848672000 (142423838289717 / 50000)
      (142430325767597 / 50000) := by
  exact
    packedTile65536 2848540928 2848672000 14 5960 53371 31 _ _ (1088503 / 50000) (2177009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2848672000 :
    ThetaLowerSegment 2848672000 2848803072 (142430325767597 / 50000) (71218437651091 / 25000) := by
  exact
    packedTile65536 2848672000 2848803072 14 6017 53372 31 _ _ (217701 / 10000) (2177013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2848803072 :
    ThetaLowerSegment 2848803072 2848934144 (71218437651091 / 25000)
      (284886819225409 / 100000) := by
  exact
    packedTile65536 2848803072 2848934144 14 6003 53374 31 _ _ (435403 / 20000) (1088509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2848934144 :
    ThetaLowerSegment 2848934144 2849065216 (284886819225409 / 100000)
      (284899907469649 / 100000) := by
  exact
    packedTile65536 2848934144 2849065216 14 6012 53375 31 _ _ (108851 / 5000) (2177023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2849065216 :
    ThetaLowerSegment 2849065216 2849196288 (284899907469649 / 100000)
      (284912973967697 / 100000) := by
  exact
    packedTile65536 2849065216 2849196288 14 6002 53376 31 _ _ (68032 / 3125) (2177027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2849196288 :
    ThetaLowerSegment 2849196288 2849327360 (284912973967697 / 100000)
      (28492611669177 / 10000) := by
  exact
    packedTile65536 2849196288 2849327360 14 6037 53377 31 _ _ (2177029 / 100000) (272129 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2849327360 :
    ThetaLowerSegment 2849327360 2849458432 (28492611669177 / 10000) (1139757238047 / 400) := by
  exact
    packedTile65536 2849327360 2849458432 14 6060 53379 31 _ _ (2177033 / 100000) (544259 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2849458432 :
    ThetaLowerSegment 2849458432 2849589504 (1139757238047 / 400) (8904764542262 / 3125) := by
  exact
    packedTile65536 2849458432 2849589504 14 6043 53380 31 _ _ (1088519 / 50000) (2177041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2849589504 :
    ThetaLowerSegment 2849589504 2849720576 (8904764542262 / 3125) (284965686534523 / 100000) := by
  exact
    packedTile65536 2849589504 2849720576 14 6073 53381 31 _ _ (2177043 / 100000) (1088523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2849720576 :
    ThetaLowerSegment 2849720576 2849851648 (284965686534523 / 100000)
      (71244743263091 / 25000) := by
  exact
    packedTile65536 2849720576 2849851648 14 6103 53382 31 _ _ (2177047 / 100000) (43541 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2849851648 :
    ThetaLowerSegment 2849851648 2849982720 (71244743263091 / 25000) (14249601550513 / 5000) := by
  exact
    packedTile65536 2849851648 2849982720 14 5998 53384 31 _ _ (544263 / 25000) (435411 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2849982720 :
    ThetaLowerSegment 2849982720 2850113792 (14249601550513 / 5000) (71251294018597 / 25000) := by
  exact
    packedTile65536 2849982720 2850113792 14 6038 53385 31 _ _ (68033 / 3125) (2177059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2850113792 :
    ThetaLowerSegment 2850113792 2850244864 (71251294018597 / 25000)
      (285018288512791 / 100000) := by
  exact
    packedTile65536 2850113792 2850244864 14 6023 53386 31 _ _ (2177061 / 100000) (272133 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2850244864 :
    ThetaLowerSegment 2850244864 2850375936 (285018288512791 / 100000)
      (285031329138131 / 100000) := by
  exact
    packedTile65536 2850244864 2850375936 14 5990 53387 31 _ _ (1088533 / 50000) (2177069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2850375936 :
    ThetaLowerSegment 2850375936 2850507008 (285031329138131 / 100000)
      (285044278350491 / 100000) := by
  exact
    packedTile65536 2850375936 2850507008 14 5948 53388 31 _ _ (217707 / 10000) (2177073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2850507008 :
    ThetaLowerSegment 2850507008 2850638080 (285044278350491 / 100000)
      (285057353862941 / 100000) := by
  exact
    packedTile65536 2850507008 2850638080 14 6006 53390 31 _ _ (87083 / 4000) (1088539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2850638080 :
    ThetaLowerSegment 2850638080 2850769152 (285057353862941 / 100000)
      (285070368441203 / 100000) := by
  exact
    packedTile65536 2850638080 2850769152 14 5978 53391 31 _ _ (2177079 / 100000) (1088541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2850769152 :
    ThetaLowerSegment 2850769152 2850900224 (285070368441203 / 100000) (11403342288643 / 4000) := by
  exact
    packedTile65536 2850769152 2850900224 14 6058 53392 31 _ _ (544271 / 25000) (2177087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2850900224 :
    ThetaLowerSegment 2850900224 2851031296 (11403342288643 / 4000) (17818541591809 / 6250) := by
  exact
    packedTile65536 2850900224 2851031296 14 6021 53393 31 _ _ (2177089 / 100000) (544273 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2851031296 :
    ThetaLowerSegment 2851031296 2851162368 (17818541591809 / 6250) (142554848773821 / 50000) := by
  exact
    packedTile65536 2851031296 2851162368 14 5986 53395 31 _ _ (2177093 / 100000) (272137 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2851162368 :
    ThetaLowerSegment 2851162368 2851293440 (142554848773821 / 50000) (71280716703361 / 25000) := by
  exact
    packedTile65536 2851162368 2851293440 14 6049 53396 31 _ _ (1088549 / 50000) (2177101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2851293440 :
    ThetaLowerSegment 2851293440 2851424512 (71280716703361 / 25000) (71283991064769 / 25000) := by
  exact
    packedTile65536 2851293440 2851424512 14 6016 53397 31 _ _ (1088551 / 50000) (435421 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2851424512 :
    ThetaLowerSegment 2851424512 2851555584 (71283991064769 / 25000) (14257459182639 / 5000) := by
  exact
    packedTile65536 2851424512 2851555584 14 6072 53398 31 _ _ (2177107 / 100000) (217711 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2851555584 :
    ThetaLowerSegment 2851555584 2851686656 (14257459182639 / 5000) (71290605667713 / 25000) := by
  exact
    packedTile65536 2851555584 2851686656 14 6081 53399 31 _ _ (272139 / 12500) (435423 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2851686656 :
    ThetaLowerSegment 2851686656 2851817728 (71290605667713 / 25000) (71293871341713 / 25000) := by
  exact
    packedTile65536 2851686656 2851817728 14 6000 53401 31 _ _ (544279 / 25000) (2177119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2851817728 :
    ThetaLowerSegment 2851817728 2851948800 (71293871341713 / 25000) (71297102189277 / 25000) := by
  exact
    packedTile65536 2851817728 2851948800 14 5936 53402 31 _ _ (2177121 / 100000) (544281 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2851948800 :
    ThetaLowerSegment 2851948800 2852079872 (71297102189277 / 25000)
      (285201678333983 / 100000) := by
  exact
    packedTile65536 2851948800 2852079872 14 6095 53403 31 _ _ (17417 / 800) (272141 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2852079872 :
    ThetaLowerSegment 2852079872 2852210944 (285201678333983 / 100000)
      (285214797719363 / 100000) := by
  exact
    packedTile65536 2852079872 2852210944 14 6026 53404 31 _ _ (217713 / 10000) (2177133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2852210944 :
    ThetaLowerSegment 2852210944 2852342016 (285214797719363 / 100000) (17826752576973 / 6250) := by
  exact
    packedTile65536 2852210944 2852342016 14 6083 53406 31 _ _ (435427 / 20000) (1088569 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2852342016 :
    ThetaLowerSegment 2852342016 2852473088 (17826752576973 / 6250) (7131028037067 / 2500) := by
  exact
    packedTile65536 2852342016 2852473088 14 6008 53407 31 _ _ (2177139 / 100000) (1088571 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2852473088 :
    ThetaLowerSegment 2852473088 2852604160 (7131028037067 / 2500) (17828399176317 / 6250) := by
  exact
    packedTile65536 2852473088 2852604160 14 6093 53408 31 _ _ (272143 / 12500) (2177147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2852604160 :
    ThetaLowerSegment 2852604160 2852735232 (17828399176317 / 6250) (71316853174389 / 25000) := by
  exact
    packedTile65536 2852604160 2852735232 14 5983 53409 31 _ _ (544287 / 25000) (2177151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2852735232 :
    ThetaLowerSegment 2852735232 2852866304 (71316853174389 / 25000) (228224377009 / 80) := by
  exact
    packedTile65536 2852735232 2852866304 14 5998 53411 31 _ _ (2177153 / 100000) (544289 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2852866304 :
    ThetaLowerSegment 2852866304 2852997376 (228224377009 / 80) (28529368661031 / 10000) := by
  exact
    packedTile65536 2852866304 2852997376 14 6070 53412 31 _ _ (1088579 / 50000) (2177161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2852997376 :
    ThetaLowerSegment 2852997376 2853128448 (28529368661031 / 10000) (28530666249583 / 10000) := by
  exact
    packedTile65536 2852997376 2853128448 14 5960 53413 31 _ _ (1088581 / 50000) (435433 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2853128448 :
    ThetaLowerSegment 2853128448 2853259520 (28530666249583 / 10000) (17832477128551 / 6250) := by
  exact
    packedTile65536 2853128448 2853259520 14 5958 53414 31 _ _ (2177167 / 100000) (217717 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2853259520 :
    ThetaLowerSegment 2853259520 2853390592 (17832477128551 / 6250) (3566658278101 / 1250) := by
  exact
    packedTile65536 2853259520 2853390592 14 5984 53415 31 _ _ (2177171 / 100000) (1088587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2853390592 :
    ThetaLowerSegment 2853390592 2853521664 (3566658278101 / 1250) (17834117628797 / 6250) := by
  exact
    packedTile65536 2853390592 2853521664 14 6072 53417 31 _ _ (272147 / 12500) (2177179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2853521664 :
    ThetaLowerSegment 2853521664 2853652736 (17834117628797 / 6250) (17834940602837 / 6250) := by
  exact
    packedTile65536 2853521664 2853652736 14 6048 53418 31 _ _ (108859 / 5000) (2177183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2853652736 :
    ThetaLowerSegment 2853652736 2853783808 (17834940602837 / 6250) (285372437155957 / 100000) := by
  exact
    packedTile65536 2853652736 2853783808 14 6149 53419 31 _ _ (435437 / 20000) (544297 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2853783808 :
    ThetaLowerSegment 2853783808 2853914880 (285372437155957 / 100000)
      (285385657053637 / 100000) := by
  exact
    packedTile65536 2853783808 2853914880 14 6072 53420 31 _ _ (217719 / 10000) (2177193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2853914880 :
    ThetaLowerSegment 2853914880 2854045952 (285385657053637 / 100000)
      (285398907456321 / 100000) := by
  exact
    packedTile65536 2853914880 2854045952 14 6086 53422 31 _ _ (1088597 / 50000) (2177197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2854045952 :
    ThetaLowerSegment 2854045952 2854177024 (285398907456321 / 100000)
      (285412009839903 / 100000) := by
  exact
    packedTile65536 2854045952 2854177024 14 6018 53423 31 _ _ (2177199 / 100000) (1088601 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2854177024 :
    ThetaLowerSegment 2854177024 2854308096 (285412009839903 / 100000)
      (285425033868249 / 100000) := by
  exact
    packedTile65536 2854177024 2854308096 14 5982 53424 31 _ _ (2177203 / 100000) (1088603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2854308096 :
    ThetaLowerSegment 2854308096 2854439168 (285425033868249 / 100000)
      (285437994787473 / 100000) := by
  exact
    packedTile65536 2854308096 2854439168 14 5953 53425 31 _ _ (272151 / 12500) (2177211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2854439168 :
    ThetaLowerSegment 2854439168 2854570240 (285437994787473 / 100000)
      (71362777035343 / 25000) := by
  exact
    packedTile65536 2854439168 2854570240 14 6023 53426 31 _ _ (2177213 / 100000) (68038 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2854570240 :
    ThetaLowerSegment 2854570240 2854701312 (71362777035343 / 25000) (17841519968383 / 6250) := by
  exact
    packedTile65536 2854570240 2854701312 14 6068 53428 31 _ _ (2177217 / 100000) (108861 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2854701312 :
    ThetaLowerSegment 2854701312 2854832384 (17841519968383 / 6250) (142738677261121 / 50000) := by
  exact
    packedTile65536 2854701312 2854832384 14 5987 53429 31 _ _ (1088611 / 50000) (87089 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2854832384 :
    ThetaLowerSegment 2854832384 2854963456 (142738677261121 / 50000) (35686310671531 / 12500) := by
  exact
    packedTile65536 2854832384 2854963456 14 6031 53430 31 _ _ (1088613 / 50000) (2177229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2854963456 :
    ThetaLowerSegment 2854963456 2855094528 (35686310671531 / 12500)
      (285503624961333 / 100000) := by
  exact
    packedTile65536 2854963456 2855094528 14 6035 53431 31 _ _ (2177231 / 100000) (1088617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2855094528 :
    ThetaLowerSegment 2855094528 2855225600 (285503624961333 / 100000)
      (285516675313917 / 100000) := by
  exact
    packedTile65536 2855094528 2855225600 14 5994 53433 31 _ _ (544309 / 25000) (2177239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2855225600 :
    ThetaLowerSegment 2855225600 2855356672 (285516675313917 / 100000)
      (285529799716637 / 100000) := by
  exact
    packedTile65536 2855225600 2855356672 14 6028 53434 31 _ _ (54431 / 2500) (2177243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2855356672 :
    ThetaLowerSegment 2855356672 2855487744 (285529799716637 / 100000)
      (285542719488467 / 100000) := by
  exact
    packedTile65536 2855356672 2855487744 14 5934 53435 31 _ _ (435449 / 20000) (68039 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2855487744 :
    ThetaLowerSegment 2855487744 2855618816 (285542719488467 / 100000)
      (71388941935431 / 25000) := by
  exact
    packedTile65536 2855487744 2855618816 14 5993 53436 31 _ _ (2177249 / 100000) (544313 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2855618816 :
    ThetaLowerSegment 2855618816 2855749888 (71388941935431 / 25000) (142784375353663 / 50000) := by
  exact
    packedTile65536 2855618816 2855749888 14 5963 53437 31 _ _ (1088627 / 50000) (2177257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2855749888 :
    ThetaLowerSegment 2855749888 2855880960 (142784375353663 / 50000)
      (142790937612289 / 50000) := by
  exact
    packedTile65536 2855749888 2855880960 14 6028 53439 31 _ _ (2177259 / 100000) (1088631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2855880960 :
    ThetaLowerSegment 2855880960 2856012032 (142790937612289 / 50000) (28559499105689 / 10000) := by
  exact
    packedTile65536 2855880960 2856012032 14 6024 53440 31 _ _ (2177263 / 100000) (1088633 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2856012032 :
    ThetaLowerSegment 2856012032 2856143104 (28559499105689 / 10000) (142804165588963 / 50000) := by
  exact
    packedTile65536 2856012032 2856143104 14 6127 53441 31 _ _ (544317 / 25000) (2177271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2856143104 :
    ThetaLowerSegment 2856143104 2856274176 (142804165588963 / 50000)
      (142810795382203 / 50000) := by
  exact
    packedTile65536 2856143104 2856274176 14 6090 53442 31 _ _ (272159 / 12500) (87091 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2856274176 :
    ThetaLowerSegment 2856274176 2856405248 (142810795382203 / 50000)
      (285634765467533 / 100000) := by
  exact
    packedTile65536 2856274176 2856405248 14 6051 53444 31 _ _ (2177277 / 100000) (13608 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2856405248 :
    ThetaLowerSegment 2856405248 2856536320 (285634765467533 / 100000)
      (285647829153533 / 100000) := by
  exact
    packedTile65536 2856405248 2856536320 14 6000 53445 31 _ _ (2177281 / 100000) (544321 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2856536320 :
    ThetaLowerSegment 2856536320 2856667392 (285647829153533 / 100000)
      (285661058343269 / 100000) := by
  exact
    packedTile65536 2856536320 2856667392 14 6076 53446 31 _ _ (1088643 / 50000) (2177289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2856667392 :
    ThetaLowerSegment 2856667392 2856798464 (285661058343269 / 100000)
      (142837046892243 / 50000) := by
  exact
    packedTile65536 2856667392 2856798464 14 5987 53447 31 _ _ (2177291 / 100000) (1088647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2856798464 :
    ThetaLowerSegment 2856798464 2856929536 (142837046892243 / 50000)
      (285687168440961 / 100000) := by
  exact
    packedTile65536 2856798464 2856929536 14 6005 53449 31 _ _ (435459 / 20000) (1088649 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2856929536 :
    ThetaLowerSegment 2856929536 2857060608 (285687168440961 / 100000)
      (285700428197961 / 100000) := by
  exact
    packedTile65536 2856929536 2857060608 14 6090 53450 31 _ _ (21773 / 1000) (2177303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2857060608 :
    ThetaLowerSegment 2857060608 2857191680 (285700428197961 / 100000)
      (285713566050297 / 100000) := by
  exact
    packedTile65536 2857060608 2857191680 14 6034 53451 31 _ _ (272163 / 12500) (2177307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2857191680 :
    ThetaLowerSegment 2857191680 2857322752 (285713566050297 / 100000) (5714533338371 / 2000) := by
  exact
    packedTile65536 2857191680 2857322752 14 6017 53452 31 _ _ (2177309 / 100000) (68041 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2857322752 :
    ThetaLowerSegment 2857322752 2857339136 (5714533338371 / 2000) (71432097293481 / 25000) := by
  exact
    packedTile65536 2857322752 2857339136 11 791 53453 31 _ _ (1088657 / 50000) (2177317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2857339136 :
    ThetaLowerSegment 2857339136 2857341184 (71432097293481 / 25000) (71432156080959 / 25000) := by
  exact
    packedTile65536 2857339136 2857341184 8 108 53454 31 _ _ (1088657 / 50000) (2177317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2825341184_2857341184 :
    ThetaLowerSegment 2825341184 2857341184 (282528446994899 / 100000)
      (71432156080959 / 25000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2825341184 cell2825472256)
                  (ThetaLowerSegment.join cell2825603328 cell2825734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2825865472 cell2825996544)
                  (ThetaLowerSegment.join cell2826127616 cell2826258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2826389760 cell2826520832)
                  (ThetaLowerSegment.join cell2826651904 cell2826782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2826914048 cell2827045120)
                  (ThetaLowerSegment.join cell2827176192 cell2827307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2827438336 cell2827569408)
                  (ThetaLowerSegment.join cell2827700480 cell2827831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2827962624 cell2828093696)
                  (ThetaLowerSegment.join cell2828224768 cell2828355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2828486912 cell2828617984)
                  (ThetaLowerSegment.join cell2828749056 cell2828880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2829011200 cell2829142272)
                  (ThetaLowerSegment.join cell2829273344 cell2829404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2829535488 cell2829666560)
                  (ThetaLowerSegment.join cell2829797632 cell2829928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2830059776 cell2830190848)
                  (ThetaLowerSegment.join cell2830321920 cell2830452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2830584064 cell2830715136)
                  (ThetaLowerSegment.join cell2830846208 cell2830977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2831108352 cell2831239424)
                  (ThetaLowerSegment.join cell2831370496 cell2831501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2831632640 cell2831763712)
                  (ThetaLowerSegment.join cell2831894784 cell2832025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2832156928 cell2832288000)
                  (ThetaLowerSegment.join cell2832419072 cell2832550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2832681216 cell2832812288)
                  (ThetaLowerSegment.join cell2832943360 cell2833074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2833205504 cell2833336576)
                  (ThetaLowerSegment.join cell2833467648 cell2833598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2833729792 cell2833860864)
                  (ThetaLowerSegment.join cell2833991936 cell2834123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2834254080 cell2834385152)
                  (ThetaLowerSegment.join cell2834516224 cell2834647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2834778368 cell2834909440)
                  (ThetaLowerSegment.join cell2835040512 cell2835171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2835302656 cell2835433728)
                  (ThetaLowerSegment.join cell2835564800 cell2835695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2835826944 cell2835958016)
                  (ThetaLowerSegment.join cell2836089088 cell2836220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2836351232 cell2836482304)
                  (ThetaLowerSegment.join cell2836613376 cell2836744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2836875520 cell2837006592)
                  (ThetaLowerSegment.join cell2837137664 cell2837268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2837399808 cell2837530880)
                  (ThetaLowerSegment.join cell2837661952 cell2837793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2837924096 cell2838055168)
                  (ThetaLowerSegment.join cell2838186240 cell2838317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2838448384 cell2838579456)
                  (ThetaLowerSegment.join cell2838710528 cell2838841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2838972672 cell2839103744)
                  (ThetaLowerSegment.join cell2839234816 cell2839365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2839496960 cell2839628032)
                  (ThetaLowerSegment.join cell2839759104 cell2839890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2840021248 cell2840152320)
                  (ThetaLowerSegment.join cell2840283392 cell2840414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2840545536 cell2840676608)
                  (ThetaLowerSegment.join cell2840807680 cell2840938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2841069824 cell2841200896)
                  (ThetaLowerSegment.join cell2841331968 cell2841463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2841594112 cell2841725184)
                  (ThetaLowerSegment.join cell2841856256 cell2841987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2842118400 cell2842249472)
                  (ThetaLowerSegment.join cell2842380544 cell2842511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2842642688 cell2842773760)
                  (ThetaLowerSegment.join cell2842904832 cell2843035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2843166976 cell2843298048)
                  (ThetaLowerSegment.join cell2843429120 cell2843560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2843691264 cell2843822336)
                  (ThetaLowerSegment.join cell2843953408 cell2844084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2844215552 cell2844346624)
                  (ThetaLowerSegment.join cell2844477696 cell2844608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2844739840 cell2844870912)
                  (ThetaLowerSegment.join cell2845001984 cell2845133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2845264128 cell2845395200)
                  (ThetaLowerSegment.join cell2845526272 cell2845657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2845788416 cell2845919488)
                  (ThetaLowerSegment.join cell2846050560 cell2846181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2846312704 cell2846443776)
                  (ThetaLowerSegment.join cell2846574848 cell2846705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2846836992 cell2846968064)
                  (ThetaLowerSegment.join cell2847099136 cell2847230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2847361280 cell2847492352)
                  (ThetaLowerSegment.join cell2847623424 cell2847754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2847885568 cell2848016640)
                  (ThetaLowerSegment.join cell2848147712 cell2848278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2848409856 cell2848540928)
                  (ThetaLowerSegment.join cell2848672000 cell2848803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2848934144 cell2849065216)
                  (ThetaLowerSegment.join cell2849196288 cell2849327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2849458432 cell2849589504)
                  (ThetaLowerSegment.join cell2849720576 cell2849851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2849982720 cell2850113792)
                  (ThetaLowerSegment.join cell2850244864 cell2850375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2850507008 cell2850638080)
                  (ThetaLowerSegment.join cell2850769152 cell2850900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2851031296 cell2851162368)
                  (ThetaLowerSegment.join cell2851293440 cell2851424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2851555584 cell2851686656)
                  (ThetaLowerSegment.join cell2851817728 cell2851948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2852079872 cell2852210944)
                  (ThetaLowerSegment.join cell2852342016 cell2852473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2852604160 cell2852735232)
                  (ThetaLowerSegment.join cell2852866304 cell2852997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2853128448 cell2853259520)
                  (ThetaLowerSegment.join cell2853390592 cell2853521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2853652736 cell2853783808)
                  (ThetaLowerSegment.join cell2853914880 cell2854045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2854177024 cell2854308096)
                  (ThetaLowerSegment.join cell2854439168 cell2854570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2854701312 cell2854832384)
                  (ThetaLowerSegment.join cell2854963456 cell2855094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2855225600 cell2855356672)
                  (ThetaLowerSegment.join cell2855487744 cell2855618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2855749888 cell2855880960)
                  (ThetaLowerSegment.join cell2856012032 cell2856143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2856274176 cell2856405248)
                  (ThetaLowerSegment.join cell2856536320 cell2856667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2856798464 cell2856929536)
                (ThetaLowerSegment.join cell2857060608 cell2857191680))
              (ThetaLowerSegment.join cell2857322752 cell2857339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
