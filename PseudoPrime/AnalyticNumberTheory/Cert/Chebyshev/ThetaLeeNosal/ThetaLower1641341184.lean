/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1641341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1609341184 :
    ThetaLowerSegment 1609341184 1609472256 (160929803158833 / 100000)
      (160942910549997 / 100000) := by
  exact
    packedTile65536 1609341184 1609472256 14 6183 40116 31 _ _ (529977 / 25000) (2119911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1609472256 :
    ThetaLowerSegment 1609472256 1609603328 (160942910549997 / 100000)
      (160956181224157 / 100000) := by
  exact
    packedTile65536 1609472256 1609603328 14 6260 40118 31 _ _ (529979 / 25000) (2119919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1609603328 :
    ThetaLowerSegment 1609603328 1609734400 (160956181224157 / 100000)
      (160969301433793 / 100000) := by
  exact
    packedTile65536 1609603328 1609734400 14 6189 40119 31 _ _ (529981 / 25000) (2119927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1609734400 :
    ThetaLowerSegment 1609734400 1609865472 (160969301433793 / 100000)
      (160982381414233 / 100000) := by
  exact
    packedTile65536 1609734400 1609865472 14 6170 40121 31 _ _ (529983 / 25000) (423987 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1609865472 :
    ThetaLowerSegment 1609865472 1609996544 (160982381414233 / 100000)
      (160995476283613 / 100000) := by
  exact
    packedTile65536 1609865472 1609996544 14 6177 40123 31 _ _ (105997 / 5000) (2119943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1609996544 :
    ThetaLowerSegment 1609996544 1610127616 (160995476283613 / 100000)
      (161008524563553 / 100000) := by
  exact
    packedTile65536 1609996544 1610127616 14 6155 40124 31 _ _ (529987 / 25000) (2119951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1610127616 :
    ThetaLowerSegment 1610127616 1610258688 (161008524563553 / 100000)
      (161021617411809 / 100000) := by
  exact
    packedTile65536 1610127616 1610258688 14 6176 40126 31 _ _ (529989 / 25000) (2119959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1610258688 :
    ThetaLowerSegment 1610258688 1610389760 (161021617411809 / 100000)
      (161034646716699 / 100000) := by
  exact
    packedTile65536 1610258688 1610389760 14 6146 40128 31 _ _ (423993 / 20000) (66249 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1610389760 :
    ThetaLowerSegment 1610389760 1610520832 (161034646716699 / 100000)
      (20130969843713 / 12500) := by
  exact
    packedTile65536 1610389760 1610520832 14 6185 40129 31 _ _ (2119973 / 100000) (264997 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1610520832 :
    ThetaLowerSegment 1610520832 1610651904 (20130969843713 / 12500) (32212138550757 / 20000) := by
  exact
    packedTile65536 1610520832 1610651904 14 6101 40131 31 _ _ (2119981 / 100000) (132499 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1610651904 :
    ThetaLowerSegment 1610651904 1610782976 (32212138550757 / 20000) (6442950075441 / 4000) := by
  exact
    packedTile65536 1610651904 1610782976 14 6160 40132 31 _ _ (2119989 / 100000) (264999 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1610782976 :
    ThetaLowerSegment 1610782976 1610914048 (6442950075441 / 4000) (161086912827401 / 100000) := by
  exact
    packedTile65536 1610782976 1610914048 14 6208 40134 31 _ _ (2119997 / 100000) (106 / 5)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1610914048 :
    ThetaLowerSegment 1610914048 1611045120 (161086912827401 / 100000)
      (161099904218041 / 100000) := by
  exact
    packedTile65536 1610914048 1611045120 14 6128 40136 31 _ _ (424001 / 20000) (265001 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1611045120 :
    ThetaLowerSegment 1611045120 1611176192 (161099904218041 / 100000)
      (80556465848963 / 50000) := by
  exact
    packedTile65536 1611045120 1611176192 14 6145 40137 31 _ _ (2120013 / 100000) (132501 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1611176192 :
    ThetaLowerSegment 1611176192 1611307264 (80556465848963 / 50000) (4028149086829 / 2500) := by
  exact
    packedTile65536 1611176192 1611307264 14 6147 40139 31 _ _ (1060011 / 50000) (84801 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1611307264 :
    ThetaLowerSegment 1611307264 1611438336 (4028149086829 / 2500) (16113919034033 / 10000) := by
  exact
    packedTile65536 1611307264 1611438336 14 6239 40141 31 _ _ (212003 / 10000) (2120033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1611438336 :
    ThetaLowerSegment 1611438336 1611569408 (16113919034033 / 10000) (80576127007243 / 50000) := by
  exact
    packedTile65536 1611438336 1611569408 14 6162 40142 31 _ _ (1060019 / 50000) (2120041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1611569408 :
    ThetaLowerSegment 1611569408 1611700480 (80576127007243 / 50000) (2014565862211 / 1250) := by
  exact
    packedTile65536 1611569408 1611700480 14 6139 40144 31 _ _ (1060023 / 50000) (2120049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1611700480 :
    ThetaLowerSegment 1611700480 1611831552 (2014565862211 / 1250) (80589239516677 / 50000) := by
  exact
    packedTile65536 1611700480 1611831552 14 6231 40145 31 _ _ (1060027 / 50000) (2120057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1611831552 :
    ThetaLowerSegment 1611831552 1611962624 (80589239516677 / 50000) (40297888363927 / 25000) := by
  exact
    packedTile65536 1611831552 1611962624 14 6167 40147 31 _ _ (1060031 / 50000) (424013 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1611962624 :
    ThetaLowerSegment 1611962624 1612093696 (40297888363927 / 25000) (80602345764749 / 50000) := by
  exact
    packedTile65536 1611962624 1612093696 14 6197 40149 31 _ _ (212007 / 10000) (2120073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1612093696 :
    ThetaLowerSegment 1612093696 1612224768 (80602345764749 / 50000) (80608888325457 / 50000) := by
  exact
    packedTile65536 1612093696 1612224768 14 6172 40150 31 _ _ (1060039 / 50000) (2120081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1612224768 :
    ThetaLowerSegment 1612224768 1612355840 (80608888325457 / 50000)
      (161230974192489 / 100000) := by
  exact
    packedTile65536 1612224768 1612355840 14 6225 40152 31 _ _ (2120087 / 100000) (212009 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1612355840 :
    ThetaLowerSegment 1612355840 1612486912 (161230974192489 / 100000)
      (161244229026429 / 100000) := by
  exact
    packedTile65536 1612355840 1612486912 14 6252 40154 31 _ _ (424019 / 20000) (1060049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1612486912 :
    ThetaLowerSegment 1612486912 1612617984 (161244229026429 / 100000)
      (40314326985459 / 25000) := by
  exact
    packedTile65536 1612486912 1612617984 14 6169 40155 31 _ _ (2120103 / 100000) (1060053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1612617984 :
    ThetaLowerSegment 1612617984 1612749056 (40314326985459 / 25000) (5039705089869 / 3125) := by
  exact
    packedTile65536 1612617984 1612749056 14 6252 40157 31 _ _ (2120111 / 100000) (1060057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1612749056 :
    ThetaLowerSegment 1612749056 1612880128 (5039705089869 / 3125) (161283697013013 / 100000) := by
  exact
    packedTile65536 1612749056 1612880128 14 6195 40159 31 _ _ (2120119 / 100000) (1060061 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1612880128 :
    ThetaLowerSegment 1612880128 1613011200 (161283697013013 / 100000)
      (32259358183473 / 20000) := by
  exact
    packedTile65536 1612880128 1613011200 14 6176 40160 31 _ _ (2120127 / 100000) (212013 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1613011200 :
    ThetaLowerSegment 1613011200 1613142272 (32259358183473 / 20000) (32261950684551 / 20000) := by
  exact
    packedTile65536 1613011200 1613142272 14 6114 40162 31 _ _ (424027 / 20000) (1060069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1613142272 :
    ThetaLowerSegment 1613142272 1613273344 (32261950684551 / 20000) (32264541499297 / 20000) := by
  exact
    packedTile65536 1613142272 1613273344 14 6110 40163 31 _ _ (2120143 / 100000) (1060073 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1613273344 :
    ThetaLowerSegment 1613273344 1613404416 (32264541499297 / 20000)
      (161335907562837 / 100000) := by
  exact
    packedTile65536 1613273344 1613404416 14 6226 40165 31 _ _ (265019 / 12500) (424031 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1613404416 :
    ThetaLowerSegment 1613404416 1613535488 (161335907562837 / 100000)
      (161349141601557 / 100000) := by
  exact
    packedTile65536 1613404416 1613535488 14 6242 40167 31 _ _ (13251 / 625) (2120163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1613535488 :
    ThetaLowerSegment 1613535488 1613666560 (161349141601557 / 100000)
      (161362176394421 / 100000) := by
  exact
    packedTile65536 1613535488 1613666560 14 6148 40168 31 _ _ (265021 / 12500) (2120171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1613666560 :
    ThetaLowerSegment 1613666560 1613797632 (161362176394421 / 100000)
      (161375296043509 / 100000) := by
  exact
    packedTile65536 1613666560 1613797632 14 6188 40170 31 _ _ (132511 / 6250) (2120179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1613797632 :
    ThetaLowerSegment 1613797632 1613928704 (161375296043509 / 100000)
      (161388509030197 / 100000) := by
  exact
    packedTile65536 1613797632 1613928704 14 6232 40172 31 _ _ (265023 / 12500) (2120187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1613928704 :
    ThetaLowerSegment 1613928704 1614059776 (161388509030197 / 100000)
      (32280326179697 / 20000) := by
  exact
    packedTile65536 1613928704 1614059776 14 6189 40173 31 _ _ (66256 / 3125) (424039 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1614059776 :
    ThetaLowerSegment 1614059776 1614190848 (32280326179697 / 20000) (32282934873777 / 20000) := by
  exact
    packedTile65536 1614059776 1614190848 14 6152 40175 31 _ _ (10601 / 500) (2120203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1614190848 :
    ThetaLowerSegment 1614190848 1614321920 (32282934873777 / 20000) (32285551210449 / 20000) := by
  exact
    packedTile65536 1614190848 1614321920 14 6170 40176 31 _ _ (132513 / 6250) (2120211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1614321920 :
    ThetaLowerSegment 1614321920 1614452992 (32285551210449 / 20000) (80720417835459 / 50000) := by
  exact
    packedTile65536 1614321920 1614452992 14 6169 40178 31 _ _ (2120217 / 100000) (106011 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1614452992 :
    ThetaLowerSegment 1614452992 1614584064 (80720417835459 / 50000) (5045434920599 / 3125) := by
  exact
    packedTile65536 1614452992 1614584064 14 6170 40180 31 _ _ (84809 / 4000) (530057 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1614584064 :
    ThetaLowerSegment 1614584064 1614715136 (5045434920599 / 3125) (161466882683963 / 100000) := by
  exact
    packedTile65536 1614584064 1614715136 14 6115 40181 31 _ _ (2120233 / 100000) (530059 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1614715136 :
    ThetaLowerSegment 1614715136 1614846208 (161466882683963 / 100000)
      (161479934887559 / 100000) := by
  exact
    packedTile65536 1614715136 1614846208 14 6156 40183 31 _ _ (2120241 / 100000) (530061 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1614846208 :
    ThetaLowerSegment 1614846208 1614977280 (161479934887559 / 100000)
      (80746551877049 / 50000) := by
  exact
    packedTile65536 1614846208 1614977280 14 6211 40185 31 _ _ (2120249 / 100000) (530063 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1614977280 :
    ThetaLowerSegment 1614977280 1615108352 (80746551877049 / 50000)
      (161506158176447 / 100000) := by
  exact
    packedTile65536 1614977280 1615108352 14 6157 40186 31 _ _ (2120257 / 100000) (106013 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1615108352 :
    ThetaLowerSegment 1615108352 1615239424 (161506158176447 / 100000)
      (80759718698071 / 50000) := by
  exact
    packedTile65536 1615108352 1615239424 14 6263 40188 31 _ _ (424053 / 20000) (530067 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1615239424 :
    ThetaLowerSegment 1615239424 1615370496 (80759718698071 / 50000)
      (161532547044101 / 100000) := by
  exact
    packedTile65536 1615239424 1615370496 14 6183 40190 31 _ _ (2120273 / 100000) (530069 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1615370496 :
    ThetaLowerSegment 1615370496 1615501568 (161532547044101 / 100000)
      (161545588898683 / 100000) := by
  exact
    packedTile65536 1615370496 1615501568 14 6151 40191 31 _ _ (1060141 / 50000) (424057 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1615501568 :
    ThetaLowerSegment 1615501568 1615632640 (161545588898683 / 100000)
      (161558717734363 / 100000) := by
  exact
    packedTile65536 1615501568 1615632640 14 6192 40193 31 _ _ (212029 / 10000) (2120293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1615632640 :
    ThetaLowerSegment 1615632640 1615763712 (161558717734363 / 100000)
      (161571753326467 / 100000) := by
  exact
    packedTile65536 1615632640 1615763712 14 6148 40194 31 _ _ (1060149 / 50000) (2120301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1615763712 :
    ThetaLowerSegment 1615763712 1615894784 (161571753326467 / 100000)
      (161584971314071 / 100000) := by
  exact
    packedTile65536 1615763712 1615894784 14 6234 40196 31 _ _ (1060153 / 50000) (2120309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1615894784 :
    ThetaLowerSegment 1615894784 1616025856 (161584971314071 / 100000)
      (161598153306209 / 100000) := by
  exact
    packedTile65536 1615894784 1616025856 14 6217 40198 31 _ _ (1060157 / 50000) (2120317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1616025856 :
    ThetaLowerSegment 1616025856 1616156928 (161598153306209 / 100000)
      (161611301422931 / 100000) := by
  exact
    packedTile65536 1616025856 1616156928 14 6201 40199 31 _ _ (1060161 / 50000) (84813 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1616156928 :
    ThetaLowerSegment 1616156928 1616288000 (161611301422931 / 100000)
      (161624343572761 / 100000) := by
  exact
    packedTile65536 1616156928 1616288000 14 6151 40201 31 _ _ (212033 / 10000) (2120333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1616288000 :
    ThetaLowerSegment 1616288000 1616419072 (161624343572761 / 100000)
      (161637470585319 / 100000) := by
  exact
    packedTile65536 1616288000 1616419072 14 6191 40203 31 _ _ (1060169 / 50000) (2120341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1616419072 :
    ThetaLowerSegment 1616419072 1616550144 (161637470585319 / 100000)
      (161650606128789 / 100000) := by
  exact
    packedTile65536 1616419072 1616550144 14 6195 40204 31 _ _ (1060173 / 50000) (2120349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1616550144 :
    ThetaLowerSegment 1616550144 1616681216 (161650606128789 / 100000)
      (80831811494067 / 50000) := by
  exact
    packedTile65536 1616550144 1616681216 14 6139 40206 31 _ _ (424071 / 20000) (1060179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1616681216 :
    ThetaLowerSegment 1616681216 1616812288 (80831811494067 / 50000) (3233532501081 / 2000) := by
  exact
    packedTile65536 1616681216 1616812288 14 6132 40207 31 _ _ (2120363 / 100000) (1060183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1616812288 :
    ThetaLowerSegment 1616812288 1616943360 (3233532501081 / 2000) (161689769233879 / 100000) := by
  exact
    packedTile65536 1616812288 1616943360 14 6199 40209 31 _ _ (2120371 / 100000) (1060187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1616943360 :
    ThetaLowerSegment 1616943360 1617074432 (161689769233879 / 100000)
      (80851454611271 / 50000) := by
  exact
    packedTile65536 1616943360 1617074432 14 6197 40211 31 _ _ (2120379 / 100000) (1060191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1617074432 :
    ThetaLowerSegment 1617074432 1617205504 (80851454611271 / 50000) (40429036169549 / 25000) := by
  exact
    packedTile65536 1617074432 1617205504 14 6242 40212 31 _ _ (2120387 / 100000) (212039 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1617205504 :
    ThetaLowerSegment 1617205504 1617336576 (40429036169549 / 25000)
      (161729255080481 / 100000) := by
  exact
    packedTile65536 1617205504 1617336576 14 6183 40214 31 _ _ (424079 / 20000) (1060199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1617336576 :
    ThetaLowerSegment 1617336576 1617467648 (161729255080481 / 100000)
      (161742278595707 / 100000) := by
  exact
    packedTile65536 1617336576 1617467648 14 6142 40216 31 _ _ (2120403 / 100000) (1060203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1617467648 :
    ThetaLowerSegment 1617467648 1617598720 (161742278595707 / 100000)
      (80877624574897 / 50000) := by
  exact
    packedTile65536 1617467648 1617598720 14 6117 40217 31 _ _ (2120411 / 100000) (1060207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1617598720 :
    ThetaLowerSegment 1617598720 1617729792 (80877624574897 / 50000) (20221030914783 / 12500) := by
  exact
    packedTile65536 1617598720 1617729792 14 6130 40219 31 _ _ (2120419 / 100000) (1060211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1617729792 :
    ThetaLowerSegment 1617729792 1617860864 (20221030914783 / 12500) (40445350611843 / 25000) := by
  exact
    packedTile65536 1617729792 1617860864 14 6204 40221 31 _ _ (2120427 / 100000) (212043 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1617860864 :
    ThetaLowerSegment 1617860864 1617991936 (40445350611843 / 25000) (10112151502803 / 6250) := by
  exact
    packedTile65536 1617860864 1617991936 14 6141 40222 31 _ _ (530109 / 25000) (2120439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1617991936 :
    ThetaLowerSegment 1617991936 1618123008 (10112151502803 / 6250) (40451901711299 / 25000) := by
  exact
    packedTile65536 1617991936 1618123008 14 6217 40224 31 _ _ (530111 / 25000) (2120447 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1618123008 :
    ThetaLowerSegment 1618123008 1618254080 (40451901711299 / 25000) (40455183110769 / 25000) := by
  exact
    packedTile65536 1618123008 1618254080 14 6190 40225 31 _ _ (530113 / 25000) (424091 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1618254080 :
    ThetaLowerSegment 1618254080 1618385152 (40455183110769 / 25000) (40458460281699 / 25000) := by
  exact
    packedTile65536 1618254080 1618385152 14 6182 40227 31 _ _ (106023 / 5000) (2120463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1618385152 :
    ThetaLowerSegment 1618385152 1618516224 (40458460281699 / 25000) (20230854154279 / 12500) := by
  exact
    packedTile65536 1618385152 1618516224 14 6127 40229 31 _ _ (530117 / 25000) (2120471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1618516224 :
    ThetaLowerSegment 1618516224 1618647296 (20230854154279 / 12500) (20232485860561 / 12500) := by
  exact
    packedTile65536 1618516224 1618647296 14 6156 40230 31 _ _ (530119 / 25000) (2120479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1618647296 :
    ThetaLowerSegment 1618647296 1618778368 (20232485860561 / 12500) (40468280206283 / 25000) := by
  exact
    packedTile65536 1618647296 1618778368 14 6241 40232 31 _ _ (530121 / 25000) (2120487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1618778368 :
    ThetaLowerSegment 1618778368 1618909440 (40468280206283 / 25000) (10117884718091 / 6250) := by
  exact
    packedTile65536 1618778368 1618909440 14 6147 40234 31 _ _ (530123 / 25000) (424099 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1618909440 :
    ThetaLowerSegment 1618909440 1619040512 (10117884718091 / 6250) (40474825117239 / 25000) := by
  exact
    packedTile65536 1618909440 1619040512 14 6199 40235 31 _ _ (4241 / 200) (2120503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1619040512 :
    ThetaLowerSegment 1619040512 1619171584 (40474825117239 / 25000) (5059757030163 / 3125) := by
  exact
    packedTile65536 1619040512 1619171584 14 6095 40237 31 _ _ (530127 / 25000) (2120511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1619171584 :
    ThetaLowerSegment 1619171584 1619302656 (5059757030163 / 3125) (161925382773201 / 100000) := by
  exact
    packedTile65536 1619171584 1619302656 14 6205 40238 31 _ _ (2120517 / 100000) (53013 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1619302656 :
    ThetaLowerSegment 1619302656 1619433728 (161925382773201 / 100000)
      (161938428243001 / 100000) := by
  exact
    packedTile65536 1619302656 1619433728 14 6152 40240 31 _ _ (84821 / 4000) (132533 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1619433728 :
    ThetaLowerSegment 1619433728 1619564800 (161938428243001 / 100000)
      (161951668851053 / 100000) := by
  exact
    packedTile65536 1619433728 1619564800 14 6244 40242 31 _ _ (2120533 / 100000) (265067 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1619564800 :
    ThetaLowerSegment 1619564800 1619695872 (161951668851053 / 100000)
      (80982396439651 / 50000) := by
  exact
    packedTile65536 1619564800 1619695872 14 6189 40243 31 _ _ (2120541 / 100000) (66267 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1619695872 :
    ThetaLowerSegment 1619695872 1619826944 (80982396439651 / 50000) (80988868355199 / 50000) := by
  exact
    packedTile65536 1619695872 1619826944 14 6104 40245 31 _ _ (2120549 / 100000) (265069 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1619826944 :
    ThetaLowerSegment 1619826944 1619958016 (80988868355199 / 50000) (80995340295163 / 50000) := by
  exact
    packedTile65536 1619826944 1619958016 14 6104 40247 31 _ _ (2120557 / 100000) (26507 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1619958016 :
    ThetaLowerSegment 1619958016 1620089088 (80995340295163 / 50000)
      (162003775079201 / 100000) := by
  exact
    packedTile65536 1619958016 1620089088 14 6175 40248 31 _ _ (424113 / 20000) (265071 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1620089088 :
    ThetaLowerSegment 1620089088 1620220160 (162003775079201 / 100000)
      (81008377553267 / 50000) := by
  exact
    packedTile65536 1620089088 1620220160 14 6121 40250 31 _ _ (2120573 / 100000) (66268 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1620220160 :
    ThetaLowerSegment 1620220160 1620351232 (81008377553267 / 50000)
      (162030015099527 / 100000) := by
  exact
    packedTile65536 1620220160 1620351232 14 6253 40251 31 _ _ (2120581 / 100000) (265073 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1620351232 :
    ThetaLowerSegment 1620351232 1620482304 (162030015099527 / 100000)
      (162043234851353 / 100000) := by
  exact
    packedTile65536 1620351232 1620482304 14 6234 40253 31 _ _ (2120589 / 100000) (132537 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1620482304 :
    ThetaLowerSegment 1620482304 1620613376 (162043234851353 / 100000)
      (81028145683541 / 50000) := by
  exact
    packedTile65536 1620482304 1620613376 14 6157 40255 31 _ _ (2120597 / 100000) (10603 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1620613376 :
    ThetaLowerSegment 1620613376 1620744448 (81028145683541 / 50000) (10129344849169 / 6250) := by
  exact
    packedTile65536 1620613376 1620744448 14 6237 40256 31 _ _ (1060303 / 50000) (2120609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1620744448 :
    ThetaLowerSegment 1620744448 1620875520 (10129344849169 / 6250) (3241654961949 / 2000) := by
  exact
    packedTile65536 1620744448 1620875520 14 6239 40258 31 _ _ (1060307 / 50000) (2120617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1620875520 :
    ThetaLowerSegment 1620875520 1621006592 (3241654961949 / 2000) (8104794267537 / 5000) := by
  exact
    packedTile65536 1620875520 1621006592 14 6195 40260 31 _ _ (1060311 / 50000) (3393 / 160)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1621006592 :
    ThetaLowerSegment 1621006592 1621137664 (8104794267537 / 5000) (1013181802457 / 625) := by
  exact
    packedTile65536 1621006592 1621137664 14 6226 40261 31 _ _ (212063 / 10000) (2120633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1621137664 :
    ThetaLowerSegment 1621137664 1621268736 (1013181802457 / 625) (20265297569013 / 12500) := by
  exact
    packedTile65536 1621137664 1621268736 14 6268 40263 31 _ _ (1060319 / 50000) (2120641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1621268736 :
    ThetaLowerSegment 1621268736 1621399808 (20265297569013 / 12500) (81067727167347 / 50000) := by
  exact
    packedTile65536 1621268736 1621399808 14 6165 40264 31 _ _ (1060323 / 50000) (2120649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1621399808 :
    ThetaLowerSegment 1621399808 1621530880 (81067727167347 / 50000) (10134291227947 / 6250) := by
  exact
    packedTile65536 1621399808 1621530880 14 6227 40266 31 _ _ (1060327 / 50000) (2120657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1621530880 :
    ThetaLowerSegment 1621530880 1621661952 (10134291227947 / 6250) (40540431791599 / 25000) := by
  exact
    packedTile65536 1621530880 1621661952 14 6162 40268 31 _ _ (1060331 / 50000) (424133 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1621661952 :
    ThetaLowerSegment 1621661952 1621793024 (40540431791599 / 25000) (81087462047903 / 50000) := by
  exact
    packedTile65536 1621661952 1621793024 14 6223 40269 31 _ _ (212067 / 10000) (2120673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1621793024 :
    ThetaLowerSegment 1621793024 1621924096 (81087462047903 / 50000) (81094019184279 / 50000) := by
  exact
    packedTile65536 1621793024 1621924096 14 6184 40271 31 _ _ (1060339 / 50000) (2120681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1621924096 :
    ThetaLowerSegment 1621924096 1622055168 (81094019184279 / 50000) (648804084833 / 400) := by
  exact
    packedTile65536 1621924096 1622055168 14 6122 40273 31 _ _ (1060343 / 50000) (2120689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1622055168 :
    ThetaLowerSegment 1622055168 1622186240 (648804084833 / 400) (20276764031539 / 12500) := by
  exact
    packedTile65536 1622055168 1622186240 14 6173 40274 31 _ _ (1060347 / 50000) (2120697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1622186240 :
    ThetaLowerSegment 1622186240 1622317312 (20276764031539 / 12500)
      (162227300904269 / 100000) := by
  exact
    packedTile65536 1622186240 1622317312 14 6219 40276 31 _ _ (2120703 / 100000) (1060353 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1622317312 :
    ThetaLowerSegment 1622317312 1622448384 (162227300904269 / 100000)
      (81120206630191 / 50000) := by
  exact
    packedTile65536 1622317312 1622448384 14 6183 40278 31 _ _ (2120711 / 100000) (1060357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1622448384 :
    ThetaLowerSegment 1622448384 1622579456 (81120206630191 / 50000) (40563374524153 / 25000) := by
  exact
    packedTile65536 1622448384 1622579456 14 6170 40279 31 _ _ (2120719 / 100000) (1060361 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1622579456 :
    ThetaLowerSegment 1622579456 1622710528 (40563374524153 / 25000) (32453311930841 / 20000) := by
  exact
    packedTile65536 1622579456 1622710528 14 6159 40281 31 _ _ (2120727 / 100000) (212073 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1622710528 :
    ThetaLowerSegment 1622710528 1622841600 (32453311930841 / 20000) (1014247818446 / 625) := by
  exact
    packedTile65536 1622710528 1622841600 14 6173 40282 31 _ _ (424147 / 20000) (1060369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1622841600 :
    ThetaLowerSegment 1622841600 1622972672 (1014247818446 / 625) (40573223217663 / 25000) := by
  exact
    packedTile65536 1622841600 1622972672 14 6244 40284 31 _ _ (2120743 / 100000) (1060373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1622972672 :
    ThetaLowerSegment 1622972672 1623103744 (40573223217663 / 25000) (20288237164473 / 12500) := by
  exact
    packedTile65536 1622972672 1623103744 14 6132 40286 31 _ _ (2120751 / 100000) (1060377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1623103744 :
    ThetaLowerSegment 1623103744 1623234816 (20288237164473 / 12500) (16231890605149 / 10000) := by
  exact
    packedTile65536 1623103744 1623234816 14 6134 40287 31 _ _ (2120759 / 100000) (1060381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1623234816 :
    ThetaLowerSegment 1623234816 1623365888 (16231890605149 / 10000) (40583025365941 / 25000) := by
  exact
    packedTile65536 1623234816 1623365888 14 6222 40289 31 _ _ (2120767 / 100000) (212077 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1623365888 :
    ThetaLowerSegment 1623365888 1623496960 (40583025365941 / 25000)
      (162345095452189 / 100000) := by
  exact
    packedTile65536 1623365888 1623496960 14 6127 40291 31 _ _ (84831 / 4000) (1060389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1623496960 :
    ThetaLowerSegment 1623496960 1623628032 (162345095452189 / 100000)
      (32471628501841 / 20000) := by
  exact
    packedTile65536 1623496960 1623628032 14 6152 40292 31 _ _ (2120783 / 100000) (1060393 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1623628032 :
    ThetaLowerSegment 1623628032 1623759104 (32471628501841 / 20000)
      (162371223548093 / 100000) := by
  exact
    packedTile65536 1623628032 1623759104 14 6168 40294 31 _ _ (2120791 / 100000) (1060397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1623759104 :
    ThetaLowerSegment 1623759104 1623890176 (162371223548093 / 100000)
      (162384253737149 / 100000) := by
  exact
    packedTile65536 1623759104 1623890176 14 6144 40295 31 _ _ (2120799 / 100000) (1060401 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1623890176 :
    ThetaLowerSegment 1623890176 1624021248 (162384253737149 / 100000)
      (162397413350789 / 100000) := by
  exact
    packedTile65536 1623890176 1624021248 14 6205 40297 31 _ _ (265101 / 12500) (2120811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1624021248 :
    ThetaLowerSegment 1624021248 1624152320 (162397413350789 / 100000)
      (162410462731637 / 100000) := by
  exact
    packedTile65536 1624021248 1624152320 14 6153 40299 31 _ _ (132551 / 6250) (2120819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1624152320 :
    ThetaLowerSegment 1624152320 1624283392 (162410462731637 / 100000)
      (162423518524181 / 100000) := by
  exact
    packedTile65536 1624152320 1624283392 14 6156 40300 31 _ _ (265103 / 12500) (2120827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1624283392 :
    ThetaLowerSegment 1624283392 1624414464 (162423518524181 / 100000)
      (162436816140821 / 100000) := by
  exact
    packedTile65536 1624283392 1624414464 14 6270 40302 31 _ _ (66276 / 3125) (424167 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1624414464 :
    ThetaLowerSegment 1624414464 1624545536 (162436816140821 / 100000)
      (162449908086141 / 100000) := by
  exact
    packedTile65536 1624414464 1624545536 14 6173 40304 31 _ _ (53021 / 2500) (2120843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1624545536 :
    ThetaLowerSegment 1624545536 1624676608 (162449908086141 / 100000)
      (162462900400989 / 100000) := by
  exact
    packedTile65536 1624545536 1624676608 14 6126 40305 31 _ _ (132553 / 6250) (2120851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1624676608 :
    ThetaLowerSegment 1624676608 1624807680 (162462900400989 / 100000)
      (162476075158461 / 100000) := by
  exact
    packedTile65536 1624676608 1624807680 14 6212 40307 31 _ _ (265107 / 12500) (2120859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1624807680 :
    ThetaLowerSegment 1624807680 1624938752 (162476075158461 / 100000)
      (162489124834653 / 100000) := by
  exact
    packedTile65536 1624807680 1624938752 14 6153 40308 31 _ _ (66277 / 3125) (2120867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1624938752 :
    ThetaLowerSegment 1624938752 1625069824 (162489124834653 / 100000) (6500091054477 / 4000) := by
  exact
    packedTile65536 1624938752 1625069824 14 6201 40310 31 _ _ (265109 / 12500) (16967 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1625069824 :
    ThetaLowerSegment 1625069824 1625200896 (6500091054477 / 4000) (6500614911837 / 4000) := by
  exact
    packedTile65536 1625069824 1625200896 14 6175 40312 31 _ _ (26511 / 1250) (2120883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1625200896 :
    ThetaLowerSegment 1625200896 1625331968 (6500614911837 / 4000) (32505706581193 / 20000) := by
  exact
    packedTile65536 1625200896 1625331968 14 6205 40313 31 _ _ (265111 / 12500) (2120891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1625331968 :
    ThetaLowerSegment 1625331968 1625463040 (32505706581193 / 20000)
      (162541561570093 / 100000) := by
  exact
    packedTile65536 1625331968 1625463040 14 6143 40315 31 _ _ (66278 / 3125) (2120899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1625463040 :
    ThetaLowerSegment 1625463040 1625594112 (162541561570093 / 100000)
      (32510928661193 / 20000) := by
  exact
    packedTile65536 1625463040 1625594112 14 6168 40317 31 _ _ (265113 / 12500) (2120907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1625594112 :
    ThetaLowerSegment 1625594112 1625725184 (32510928661193 / 20000)
      (162567725091181 / 100000) := by
  exact
    packedTile65536 1625594112 1625725184 14 6168 40318 31 _ _ (132557 / 6250) (424183 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1625725184 :
    ThetaLowerSegment 1625725184 1625856256 (162567725091181 / 100000)
      (162580652098581 / 100000) := by
  exact
    packedTile65536 1625725184 1625856256 14 6095 40320 31 _ _ (53023 / 2500) (2120923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1625856256 :
    ThetaLowerSegment 1625856256 1625987328 (162580652098581 / 100000)
      (162593861244393 / 100000) := by
  exact
    packedTile65536 1625856256 1625987328 14 6228 40321 31 _ _ (2120929 / 100000) (530233 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1625987328 :
    ThetaLowerSegment 1625987328 1626118400 (162593861244393 / 100000)
      (40651788289143 / 25000) := by
  exact
    packedTile65536 1625987328 1626118400 14 6267 40323 31 _ _ (2120937 / 100000) (106047 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1626118400 :
    ThetaLowerSegment 1626118400 1626249472 (40651788289143 / 25000)
      (162620322104077 / 100000) := by
  exact
    packedTile65536 1626118400 1626249472 14 6209 40325 31 _ _ (424189 / 20000) (530237 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1626249472 :
    ThetaLowerSegment 1626249472 1626380544 (162620322104077 / 100000)
      (162633361723121 / 100000) := by
  exact
    packedTile65536 1626249472 1626380544 14 6148 40326 31 _ _ (2120953 / 100000) (530239 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1626380544 :
    ThetaLowerSegment 1626380544 1626511616 (162633361723121 / 100000)
      (162646409875193 / 100000) := by
  exact
    packedTile65536 1626380544 1626511616 14 6152 40328 31 _ _ (2120961 / 100000) (530241 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1626511616 :
    ThetaLowerSegment 1626511616 1626642688 (162646409875193 / 100000)
      (162659496253923 / 100000) := by
  exact
    packedTile65536 1626511616 1626642688 14 6170 40330 31 _ _ (2120969 / 100000) (530243 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1626642688 :
    ThetaLowerSegment 1626642688 1626773760 (162659496253923 / 100000)
      (162672578440059 / 100000) := by
  exact
    packedTile65536 1626642688 1626773760 14 6168 40331 31 _ _ (2120977 / 100000) (106049 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1626773760 :
    ThetaLowerSegment 1626773760 1626904832 (162672578440059 / 100000) (5083928288007 / 3125) := by
  exact
    packedTile65536 1626773760 1626904832 14 6189 40333 31 _ _ (424197 / 20000) (530247 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1626904832 :
    ThetaLowerSegment 1626904832 1627035904 (5083928288007 / 3125) (32539769801969 / 20000) := by
  exact
    packedTile65536 1626904832 1627035904 14 6197 40334 31 _ _ (2120993 / 100000) (530249 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1627035904 :
    ThetaLowerSegment 1627035904 1627166976 (32539769801969 / 20000) (5084743281092 / 3125) := by
  exact
    packedTile65536 1627035904 1627166976 14 6099 40336 31 _ _ (2121001 / 100000) (530251 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1627166976 :
    ThetaLowerSegment 1627166976 1627298048 (5084743281092 / 3125) (3254495905283 / 2000) := by
  exact
    packedTile65536 1627166976 1627298048 14 6134 40338 31 _ _ (2121009 / 100000) (530253 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1627298048 :
    ThetaLowerSegment 1627298048 1627429120 (3254495905283 / 2000) (20342254331533 / 12500) := by
  exact
    packedTile65536 1627298048 1627429120 14 6242 40339 31 _ _ (2121017 / 100000) (106051 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1627429120 :
    ThetaLowerSegment 1627429120 1627560192 (20342254331533 / 12500)
      (162751187128289 / 100000) := by
  exact
    packedTile65536 1627429120 1627560192 14 6201 40341 31 _ _ (84841 / 4000) (530257 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1627560192 :
    ThetaLowerSegment 1627560192 1627691264 (162751187128289 / 100000)
      (162764282386031 / 100000) := by
  exact
    packedTile65536 1627560192 1627691264 14 6174 40343 31 _ _ (2121033 / 100000) (530259 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1627691264 :
    ThetaLowerSegment 1627691264 1627822336 (162764282386031 / 100000)
      (20347179370159 / 12500) := by
  exact
    packedTile65536 1627691264 1627822336 14 6201 40344 31 _ _ (2121041 / 100000) (530261 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1627822336 :
    ThetaLowerSegment 1627822336 1627953408 (20347179370159 / 12500) (32558103094091 / 20000) := by
  exact
    packedTile65536 1627822336 1627953408 14 6167 40346 31 _ _ (2121049 / 100000) (530263 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1627953408 :
    ThetaLowerSegment 1627953408 1628084480 (32558103094091 / 20000) (40700957336311 / 25000) := by
  exact
    packedTile65536 1627953408 1628084480 14 6277 40347 31 _ _ (2121057 / 100000) (106053 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1628084480 :
    ThetaLowerSegment 1628084480 1628215552 (40700957336311 / 25000) (20352093859153 / 12500) := by
  exact
    packedTile65536 1628084480 1628215552 14 6092 40349 31 _ _ (424213 / 20000) (530267 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1628215552 :
    ThetaLowerSegment 1628215552 1628346624 (20352093859153 / 12500) (203537175413 / 125) := by
  exact
    packedTile65536 1628215552 1628346624 14 6124 40351 31 _ _ (1060537 / 50000) (2121077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1628346624 :
    ThetaLowerSegment 1628346624 1628477696 (203537175413 / 125) (8142151975727 / 5000) := by
  exact
    packedTile65536 1628346624 1628477696 14 6270 40352 31 _ _ (1060541 / 50000) (424217 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1628477696 :
    ThetaLowerSegment 1628477696 1628608768 (8142151975727 / 5000) (3257119520849 / 2000) := by
  exact
    packedTile65536 1628477696 1628608768 14 6099 40354 31 _ _ (212109 / 10000) (2121093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1628608768 :
    ThetaLowerSegment 1628608768 1628739840 (3257119520849 / 2000) (5089666776211 / 3125) := by
  exact
    packedTile65536 1628608768 1628739840 14 6299 40356 31 _ _ (1060549 / 50000) (2121101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1628739840 :
    ThetaLowerSegment 1628739840 1628870912 (5089666776211 / 3125) (81441230060787 / 50000) := by
  exact
    packedTile65536 1628739840 1628870912 14 6187 40357 31 _ _ (1060553 / 50000) (2121109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1628870912 :
    ThetaLowerSegment 1628870912 1629001984 (81441230060787 / 50000) (8144780445363 / 5000) := by
  exact
    packedTile65536 1628870912 1629001984 14 6199 40359 31 _ _ (1060557 / 50000) (2121117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1629001984 :
    ThetaLowerSegment 1629001984 1629133056 (8144780445363 / 5000) (81454317358731 / 50000) := by
  exact
    packedTile65536 1629001984 1629133056 14 6141 40360 31 _ _ (1060561 / 50000) (16969 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1629133056 :
    ThetaLowerSegment 1629133056 1629264128 (81454317358731 / 50000) (81460867408171 / 50000) := by
  exact
    packedTile65536 1629133056 1629264128 14 6176 40362 31 _ _ (212113 / 10000) (2121133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1629264128 :
    ThetaLowerSegment 1629264128 1629395200 (81460867408171 / 50000) (81467366575003 / 50000) := by
  exact
    packedTile65536 1629264128 1629395200 14 6128 40364 31 _ _ (1060569 / 50000) (2121141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1629395200 :
    ThetaLowerSegment 1629395200 1629526272 (81467366575003 / 50000) (20368478373033 / 12500) := by
  exact
    packedTile65536 1629395200 1629526272 14 6173 40365 31 _ _ (1060573 / 50000) (2121149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1629526272 :
    ThetaLowerSegment 1629526272 1629657344 (20368478373033 / 12500) (40740271049191 / 25000) := by
  exact
    packedTile65536 1629526272 1629657344 14 6250 40367 31 _ _ (1060577 / 50000) (2121157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1629657344 :
    ThetaLowerSegment 1629657344 1629788416 (40740271049191 / 25000) (81487082701409 / 50000) := by
  exact
    packedTile65536 1629657344 1629788416 14 6167 40369 31 _ _ (1060581 / 50000) (424233 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1629788416 :
    ThetaLowerSegment 1629788416 1629919488 (81487082701409 / 50000) (40746819088647 / 25000) := by
  exact
    packedTile65536 1629788416 1629919488 14 6181 40370 31 _ _ (212117 / 10000) (2121173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1629919488 :
    ThetaLowerSegment 1629919488 1630050560 (40746819088647 / 25000) (16300044674879 / 10000) := by
  exact
    packedTile65536 1629919488 1630050560 14 6209 40372 31 _ _ (1060589 / 50000) (2121181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1630050560 :
    ThetaLowerSegment 1630050560 1630181632 (16300044674879 / 10000) (815067831421 / 500) := by
  exact
    packedTile65536 1630050560 1630181632 14 6185 40373 31 _ _ (1060593 / 50000) (2121189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1630181632 :
    ThetaLowerSegment 1630181632 1630312704 (815067831421 / 500) (16302662223327 / 10000) := by
  exact
    packedTile65536 1630181632 1630312704 14 6155 40375 31 _ _ (1060597 / 50000) (2121197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1630312704 :
    ThetaLowerSegment 1630312704 1630443776 (16302662223327 / 10000) (81519935630481 / 50000) := by
  exact
    packedTile65536 1630312704 1630443776 14 6246 40377 31 _ _ (1060601 / 50000) (424241 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1630443776 :
    ThetaLowerSegment 1630443776 1630574848 (81519935630481 / 50000) (81526564411731 / 50000) := by
  exact
    packedTile65536 1630443776 1630574848 14 6250 40378 31 _ _ (212121 / 10000) (2121213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1630574848 :
    ThetaLowerSegment 1630574848 1630705920 (81526564411731 / 50000) (81533076550991 / 50000) := by
  exact
    packedTile65536 1630574848 1630705920 14 6140 40380 31 _ _ (1060609 / 50000) (2121221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1630705920 :
    ThetaLowerSegment 1630705920 1630836992 (81533076550991 / 50000) (81539669321399 / 50000) := by
  exact
    packedTile65536 1630705920 1630836992 14 6216 40381 31 _ _ (1060613 / 50000) (2121229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1630836992 :
    ThetaLowerSegment 1630836992 1630968064 (81539669321399 / 50000) (81546141206333 / 50000) := by
  exact
    packedTile65536 1630836992 1630968064 14 6102 40383 31 _ _ (1060617 / 50000) (2121237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1630968064 :
    ThetaLowerSegment 1630968064 1631099136 (81546141206333 / 50000) (40776369664787 / 25000) := by
  exact
    packedTile65536 1630968064 1631099136 14 6221 40385 31 _ _ (1060621 / 50000) (424249 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1631099136 :
    ThetaLowerSegment 1631099136 1631230208 (40776369664787 / 25000) (81559250506449 / 50000) := by
  exact
    packedTile65536 1631099136 1631230208 14 6139 40386 31 _ _ (1697 / 80) (2121253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1631230208 :
    ThetaLowerSegment 1631230208 1631361280 (81559250506449 / 50000) (16313162736359 / 10000) := by
  exact
    packedTile65536 1631230208 1631361280 14 6188 40388 31 _ _ (2121259 / 100000) (1060631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1631361280 :
    ThetaLowerSegment 1631361280 1631492352 (16313162736359 / 10000)
      (163144679519441 / 100000) := by
  exact
    packedTile65536 1631361280 1631492352 14 6153 40390 31 _ _ (2121267 / 100000) (212127 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1631492352 :
    ThetaLowerSegment 1631492352 1631623424 (163144679519441 / 100000)
      (163157848394641 / 100000) := by
  exact
    packedTile65536 1631492352 1631623424 14 6208 40391 31 _ _ (84851 / 4000) (1060639 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1631623424 :
    ThetaLowerSegment 1631623424 1631754496 (163157848394641 / 100000) (5099092501402 / 3125) := by
  exact
    packedTile65536 1631623424 1631754496 14 6181 40393 31 _ _ (2121283 / 100000) (1060643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1631754496 :
    ThetaLowerSegment 1631754496 1631885568 (5099092501402 / 3125) (20398001278387 / 12500) := by
  exact
    packedTile65536 1631754496 1631885568 14 6152 40394 31 _ _ (2121291 / 100000) (1060647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1631885568 :
    ThetaLowerSegment 1631885568 1632016640 (20398001278387 / 12500)
      (163197138946607 / 100000) := by
  exact
    packedTile65536 1631885568 1632016640 14 6189 40396 31 _ _ (2121299 / 100000) (1060651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1632016640 :
    ThetaLowerSegment 1632016640 1632147712 (163197138946607 / 100000)
      (32642042936591 / 20000) := by
  exact
    packedTile65536 1632016640 1632147712 14 6164 40398 31 _ _ (2121307 / 100000) (212131 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1632147712 :
    ThetaLowerSegment 1632147712 1632278784 (32642042936591 / 20000) (32644677609821 / 20000) := by
  exact
    packedTile65536 1632147712 1632278784 14 6210 40399 31 _ _ (424263 / 20000) (1060659 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1632278784 :
    ThetaLowerSegment 1632278784 1632409856 (32644677609821 / 20000) (81618277550483 / 50000) := by
  exact
    packedTile65536 1632278784 1632409856 14 6207 40401 31 _ _ (2121323 / 100000) (1060663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1632409856 :
    ThetaLowerSegment 1632409856 1632540928 (81618277550483 / 50000) (20406183190179 / 12500) := by
  exact
    packedTile65536 1632409856 1632540928 14 6086 40403 31 _ _ (2121331 / 100000) (1060667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1632540928 :
    ThetaLowerSegment 1632540928 1632672000 (20406183190179 / 12500) (32652522291843 / 20000) := by
  exact
    packedTile65536 1632540928 1632672000 14 6197 40404 31 _ _ (2121339 / 100000) (1060671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1632672000 :
    ThetaLowerSegment 1632672000 1632803072 (32652522291843 / 20000) (81637933878309 / 50000) := by
  exact
    packedTile65536 1632672000 1632803072 14 6249 40406 31 _ _ (2121347 / 100000) (42427 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1632803072 :
    ThetaLowerSegment 1632803072 1632934144 (81637933878309 / 50000)
      (163289310783253 / 100000) := by
  exact
    packedTile65536 1632803072 1632934144 14 6337 40407 31 _ _ (424271 / 20000) (1060679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1632934144 :
    ThetaLowerSegment 1632934144 1633065216 (163289310783253 / 100000)
      (81651298439861 / 50000) := by
  exact
    packedTile65536 1632934144 1633065216 14 6263 40409 31 _ _ (2121363 / 100000) (1060683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1633065216 :
    ThetaLowerSegment 1633065216 1633196288 (81651298439861 / 50000)
      (163315573306129 / 100000) := by
  exact
    packedTile65536 1633065216 1633196288 14 6117 40411 31 _ _ (2121371 / 100000) (1060687 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1633196288 :
    ThetaLowerSegment 1633196288 1633327360 (163315573306129 / 100000)
      (81664421265887 / 50000) := by
  exact
    packedTile65536 1633196288 1633327360 14 6255 40412 31 _ _ (2121379 / 100000) (1060691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1633327360 :
    ThetaLowerSegment 1633327360 1633458432 (81664421265887 / 50000) (20417725525793 / 12500) := by
  exact
    packedTile65536 1633327360 1633458432 14 6110 40414 31 _ _ (2121387 / 100000) (212139 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1633458432 :
    ThetaLowerSegment 1633458432 1633589504 (20417725525793 / 12500)
      (163354958976739 / 100000) := by
  exact
    packedTile65536 1633458432 1633589504 14 6201 40416 31 _ _ (424279 / 20000) (1060699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1633589504 :
    ThetaLowerSegment 1633589504 1633720576 (163354958976739 / 100000)
      (32673614698017 / 20000) := by
  exact
    packedTile65536 1633589504 1633720576 14 6182 40417 31 _ _ (2121403 / 100000) (1060703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1633720576 :
    ThetaLowerSegment 1633720576 1633851648 (32673614698017 / 20000)
      (163381221995463 / 100000) := by
  exact
    packedTile65536 1633720576 1633851648 14 6198 40419 31 _ _ (2121411 / 100000) (1060707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1633851648 :
    ThetaLowerSegment 1633851648 1633982720 (163381221995463 / 100000) (2042429764469 / 1250) := by
  exact
    packedTile65536 1633851648 1633982720 14 6203 40420 31 _ _ (2121419 / 100000) (1060711 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1633982720 :
    ThetaLowerSegment 1633982720 1634113792 (2042429764469 / 1250) (163407514912077 / 100000) := by
  exact
    packedTile65536 1633982720 1634113792 14 6191 40422 31 _ _ (2121427 / 100000) (212143 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1634113792 :
    ThetaLowerSegment 1634113792 1634244864 (163407514912077 / 100000)
      (81710307386601 / 50000) := by
  exact
    packedTile65536 1634113792 1634244864 14 6175 40424 31 _ _ (424287 / 20000) (1060719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1634244864 :
    ThetaLowerSegment 1634244864 1634375936 (81710307386601 / 50000) (40858440869229 / 25000) := by
  exact
    packedTile65536 1634244864 1634375936 14 6198 40425 31 _ _ (2121443 / 100000) (1060723 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1634375936 :
    ThetaLowerSegment 1634375936 1634507008 (40858440869229 / 25000)
      (163446927080371 / 100000) := by
  exact
    packedTile65536 1634375936 1634507008 14 6205 40427 31 _ _ (2121451 / 100000) (1060727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1634507008 :
    ThetaLowerSegment 1634507008 1634638080 (163446927080371 / 100000)
      (163459906166533 / 100000) := by
  exact
    packedTile65536 1634507008 1634638080 14 6118 40429 31 _ _ (2121459 / 100000) (1060731 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1634638080 :
    ThetaLowerSegment 1634638080 1634769152 (163459906166533 / 100000)
      (163472948945649 / 100000) := by
  exact
    packedTile65536 1634638080 1634769152 14 6148 40430 31 _ _ (2121467 / 100000) (212147 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1634769152 :
    ThetaLowerSegment 1634769152 1634900224 (163472948945649 / 100000)
      (81743079685237 / 50000) := by
  exact
    packedTile65536 1634769152 1634900224 14 6227 40432 31 _ _ (84859 / 4000) (1060739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1634900224 :
    ThetaLowerSegment 1634900224 1635031296 (81743079685237 / 50000) (81749630824741 / 50000) := by
  exact
    packedTile65536 1634900224 1635031296 14 6176 40433 31 _ _ (2121483 / 100000) (1060743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1635031296 :
    ThetaLowerSegment 1635031296 1635162368 (81749630824741 / 50000) (81756232904733 / 50000) := by
  exact
    packedTile65536 1635031296 1635162368 14 6224 40435 31 _ _ (2121491 / 100000) (1060747 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1635162368 :
    ThetaLowerSegment 1635162368 1635293440 (81756232904733 / 50000) (40881382500077 / 25000) := by
  exact
    packedTile65536 1635162368 1635293440 14 6158 40437 31 _ _ (2121499 / 100000) (1060751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1635293440 :
    ThetaLowerSegment 1635293440 1635424512 (40881382500077 / 25000) (81769394709529 / 50000) := by
  exact
    packedTile65536 1635293440 1635424512 14 6250 40438 31 _ _ (2121507 / 100000) (212151 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1635424512 :
    ThetaLowerSegment 1635424512 1635555584 (81769394709529 / 50000) (81775865330279 / 50000) := by
  exact
    packedTile65536 1635424512 1635555584 14 6100 40440 31 _ _ (424303 / 20000) (1060759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1635555584 :
    ThetaLowerSegment 1635555584 1635686656 (81775865330279 / 50000)
      (163564898953819 / 100000) := by
  exact
    packedTile65536 1635555584 1635686656 14 6207 40442 31 _ _ (2121523 / 100000) (1060763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1635686656 :
    ThetaLowerSegment 1635686656 1635817728 (163564898953819 / 100000)
      (81788972123969 / 50000) := by
  exact
    packedTile65536 1635686656 1635817728 14 6149 40443 31 _ _ (2121531 / 100000) (1060767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1635817728 :
    ThetaLowerSegment 1635817728 1635948800 (81788972123969 / 50000) (8179554677333 / 5000) := by
  exact
    packedTile65536 1635817728 1635948800 14 6198 40445 31 _ _ (2121539 / 100000) (1060771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1635948800 :
    ThetaLowerSegment 1635948800 1636079872 (8179554677333 / 5000) (163604079535847 / 100000) := by
  exact
    packedTile65536 1635948800 1636079872 14 6121 40446 31 _ _ (2121547 / 100000) (42431 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1636079872 :
    ThetaLowerSegment 1636079872 1636210944 (163604079535847 / 100000)
      (40904299277603 / 25000) := by
  exact
    packedTile65536 1636079872 1636210944 14 6183 40448 31 _ _ (424311 / 20000) (1060779 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1636210944 :
    ThetaLowerSegment 1636210944 1636342016 (40904299277603 / 25000)
      (163630433541969 / 100000) := by
  exact
    packedTile65536 1636210944 1636342016 14 6239 40450 31 _ _ (2121563 / 100000) (1060783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1636342016 :
    ThetaLowerSegment 1636342016 1636473088 (163630433541969 / 100000)
      (163643485446761 / 100000) := by
  exact
    packedTile65536 1636342016 1636473088 14 6152 40451 31 _ _ (2121571 / 100000) (1060787 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1636473088 :
    ThetaLowerSegment 1636473088 1636604160 (163643485446761 / 100000)
      (20457076987399 / 12500) := by
  exact
    packedTile65536 1636473088 1636604160 14 6189 40453 31 _ _ (2121579 / 100000) (1060791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1636604160 :
    ThetaLowerSegment 1636604160 1636735232 (20457076987399 / 12500) (81834908206753 / 50000) := by
  exact
    packedTile65536 1636604160 1636735232 14 6222 40454 31 _ _ (2121587 / 100000) (212159 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1636735232 :
    ThetaLowerSegment 1636735232 1636866304 (81834908206753 / 50000) (40920766973969 / 25000) := by
  exact
    packedTile65536 1636735232 1636866304 14 6246 40456 31 _ _ (424319 / 20000) (1060799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1636866304 :
    ThetaLowerSegment 1636866304 1636997376 (40920766973969 / 25000) (81847977256249 / 50000) := by
  exact
    packedTile65536 1636866304 1636997376 14 6074 40458 31 _ _ (2121603 / 100000) (1060803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1636997376 :
    ThetaLowerSegment 1636997376 1637128448 (81847977256249 / 50000)
      (163709178513861 / 100000) := by
  exact
    packedTile65536 1636997376 1637128448 14 6233 40459 31 _ _ (2121611 / 100000) (1060807 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1637128448 :
    ThetaLowerSegment 1637128448 1637259520 (163709178513861 / 100000) (1309778762251 / 800) := by
  exact
    packedTile65536 1637128448 1637259520 14 6206 40461 31 _ _ (2121619 / 100000) (1060811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1637259520 :
    ThetaLowerSegment 1637259520 1637390592 (1309778762251 / 800) (40933844609009 / 25000) := by
  exact
    packedTile65536 1637259520 1637390592 14 6143 40463 31 _ _ (2121627 / 100000) (212163 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1637390592 :
    ThetaLowerSegment 1637390592 1637521664 (40933844609009 / 25000) (5117139256068 / 3125) := by
  exact
    packedTile65536 1637390592 1637521664 14 6164 40464 31 _ _ (424327 / 20000) (1060819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1637521664 :
    ThetaLowerSegment 1637521664 1637652736 (5117139256068 / 3125) (40940421689981 / 25000) := by
  exact
    packedTile65536 1637521664 1637652736 14 6236 40466 31 _ _ (2121643 / 100000) (1060823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1637652736 :
    ThetaLowerSegment 1637652736 1637783808 (40940421689981 / 25000) (40943710249031 / 25000) := by
  exact
    packedTile65536 1637652736 1637783808 14 6200 40467 31 _ _ (2121651 / 100000) (1060827 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1637783808 :
    ThetaLowerSegment 1637783808 1637914880 (40943710249031 / 25000)
      (163788048323399 / 100000) := by
  exact
    packedTile65536 1637783808 1637914880 14 6225 40469 31 _ _ (2121659 / 100000) (1060831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1637914880 :
    ThetaLowerSegment 1637914880 1638045952 (163788048323399 / 100000)
      (40950283160947 / 25000) := by
  exact
    packedTile65536 1637914880 1638045952 14 6167 40471 31 _ _ (2121667 / 100000) (212167 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1638045952 :
    ThetaLowerSegment 1638045952 1638177024 (40950283160947 / 25000) (40953529323697 / 25000) := by
  exact
    packedTile65536 1638045952 1638177024 14 6120 40472 31 _ _ (84867 / 4000) (1060839 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1638177024 :
    ThetaLowerSegment 1638177024 1638308096 (40953529323697 / 25000)
      (163827197470483 / 100000) := by
  exact
    packedTile65536 1638177024 1638308096 14 6165 40474 31 _ _ (2121683 / 100000) (1060843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1638308096 :
    ThetaLowerSegment 1638308096 1638439168 (163827197470483 / 100000)
      (32768058509467 / 20000) := by
  exact
    packedTile65536 1638308096 1638439168 14 6172 40476 31 _ _ (2121691 / 100000) (1060847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1638439168 :
    ThetaLowerSegment 1638439168 1638570240 (32768058509467 / 20000) (16385337282167 / 10000) := by
  exact
    packedTile65536 1638439168 1638570240 14 6165 40477 31 _ _ (2121699 / 100000) (1060851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1638570240 :
    ThetaLowerSegment 1638570240 1638701312 (16385337282167 / 10000) (81933183077669 / 50000) := by
  exact
    packedTile65536 1638570240 1638701312 14 6124 40479 31 _ _ (2121707 / 100000) (212171 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1638701312 :
    ThetaLowerSegment 1638701312 1638832384 (81933183077669 / 50000)
      (163879429554593 / 100000) := by
  exact
    packedTile65536 1638701312 1638832384 14 6157 40480 31 _ _ (424343 / 20000) (1060859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1638832384 :
    ThetaLowerSegment 1638832384 1638963456 (163879429554593 / 100000)
      (163892537559287 / 100000) := by
  exact
    packedTile65536 1638832384 1638963456 14 6178 40482 31 _ _ (2121723 / 100000) (1060863 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1638963456 :
    ThetaLowerSegment 1638963456 1639094528 (163892537559287 / 100000)
      (40976443759749 / 25000) := by
  exact
    packedTile65536 1638963456 1639094528 14 6239 40484 31 _ _ (2121731 / 100000) (1060867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1639094528 :
    ThetaLowerSegment 1639094528 1639225600 (40976443759749 / 25000) (81959382162577 / 50000) := by
  exact
    packedTile65536 1639094528 1639225600 14 6122 40485 31 _ _ (2121739 / 100000) (1060871 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1639225600 :
    ThetaLowerSegment 1639225600 1639356672 (81959382162577 / 50000) (40982970241277 / 25000) := by
  exact
    packedTile65536 1639225600 1639356672 14 6182 40487 31 _ _ (2121747 / 100000) (8487 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1639356672 :
    ThetaLowerSegment 1639356672 1639487744 (40982970241277 / 25000) (40986212282917 / 25000) := by
  exact
    packedTile65536 1639356672 1639487744 14 6112 40488 31 _ _ (424351 / 20000) (1060879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1639487744 :
    ThetaLowerSegment 1639487744 1639618816 (40986212282917 / 25000) (81979055075209 / 50000) := by
  exact
    packedTile65536 1639487744 1639618816 14 6250 40490 31 _ _ (2121763 / 100000) (1060883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1639618816 :
    ThetaLowerSegment 1639618816 1639749888 (81979055075209 / 50000) (32794222048267 / 20000) := by
  exact
    packedTile65536 1639618816 1639749888 14 6127 40492 31 _ _ (2121771 / 100000) (1060887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1639749888 :
    ThetaLowerSegment 1639749888 1639880960 (32794222048267 / 20000) (3279684668889 / 2000) := by
  exact
    packedTile65536 1639749888 1639880960 14 6185 40493 31 _ _ (2121779 / 100000) (1060891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1639880960 :
    ThetaLowerSegment 1639880960 1640012032 (3279684668889 / 2000) (163997390645637 / 100000) := by
  exact
    packedTile65536 1639880960 1640012032 14 6201 40495 31 _ _ (2121787 / 100000) (212179 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1640012032 :
    ThetaLowerSegment 1640012032 1640143104 (163997390645637 / 100000)
      (164010435441297 / 100000) := by
  exact
    packedTile65536 1640012032 1640143104 14 6148 40497 31 _ _ (424359 / 20000) (1060899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1640143104 :
    ThetaLowerSegment 1640143104 1640274176 (164010435441297 / 100000)
      (164023522722201 / 100000) := by
  exact
    packedTile65536 1640143104 1640274176 14 6168 40498 31 _ _ (2121803 / 100000) (1060903 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1640274176 :
    ThetaLowerSegment 1640274176 1640405248 (164023522722201 / 100000)
      (82018427030357 / 50000) := by
  exact
    packedTile65536 1640274176 1640405248 14 6283 40500 31 _ _ (2121811 / 100000) (1060907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1640405248 :
    ThetaLowerSegment 1640405248 1640536320 (82018427030357 / 50000) (5126561333078 / 3125) := by
  exact
    packedTile65536 1640405248 1640536320 14 6178 40501 31 _ _ (2121819 / 100000) (1060911 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1640536320 :
    ThetaLowerSegment 1640536320 1640667392 (5126561333078 / 3125) (32812618080429 / 20000) := by
  exact
    packedTile65536 1640536320 1640667392 14 6187 40503 31 _ _ (2121827 / 100000) (212183 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1640667392 :
    ThetaLowerSegment 1640667392 1640798464 (32812618080429 / 20000) (8203812395049 / 5000) := by
  exact
    packedTile65536 1640667392 1640798464 14 6201 40505 31 _ _ (424367 / 20000) (1060919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1640798464 :
    ThetaLowerSegment 1640798464 1640929536 (8203812395049 / 5000) (164089358768877 / 100000) := by
  exact
    packedTile65536 1640798464 1640929536 14 6179 40506 31 _ _ (2121843 / 100000) (1060923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1640929536 :
    ThetaLowerSegment 1640929536 1641060608 (164089358768877 / 100000)
      (164102688236859 / 100000) := by
  exact
    packedTile65536 1640929536 1641060608 14 6282 40508 31 _ _ (2121851 / 100000) (1060927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1641060608 :
    ThetaLowerSegment 1641060608 1641191680 (164102688236859 / 100000)
      (82057935673413 / 50000) := by
  exact
    packedTile65536 1641060608 1641191680 14 6213 40510 31 _ _ (2121859 / 100000) (1060931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1641191680 :
    ThetaLowerSegment 1641191680 1641322752 (82057935673413 / 50000) (32825748942783 / 20000) := by
  exact
    packedTile65536 1641191680 1641322752 14 6067 40511 31 _ _ (2121867 / 100000) (212187 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1641322752 :
    ThetaLowerSegment 1641322752 1641339136 (32825748942783 / 20000) (8206519033977 / 5000) := by
  exact
    packedTile65536 1641322752 1641339136 11 771 40513 31 _ _ (679 / 32) (1060939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1641339136 :
    ThetaLowerSegment 1641339136 1641341184 (8206519033977 / 5000) (41032649277723 / 25000) := by
  exact
    packedTile65536 1641339136 1641341184 8 102 40513 31 _ _ (530469 / 25000) (2121879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1609341184_1641341184 :
    ThetaLowerSegment 1609341184 1641341184 (160929803158833 / 100000)
      (41032649277723 / 25000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1609341184 cell1609472256)
                  (ThetaLowerSegment.join cell1609603328 cell1609734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1609865472 cell1609996544)
                  (ThetaLowerSegment.join cell1610127616 cell1610258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1610389760 cell1610520832)
                  (ThetaLowerSegment.join cell1610651904 cell1610782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1610914048 cell1611045120)
                  (ThetaLowerSegment.join cell1611176192 cell1611307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1611438336 cell1611569408)
                  (ThetaLowerSegment.join cell1611700480 cell1611831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1611962624 cell1612093696)
                  (ThetaLowerSegment.join cell1612224768 cell1612355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1612486912 cell1612617984)
                  (ThetaLowerSegment.join cell1612749056 cell1612880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1613011200 cell1613142272)
                  (ThetaLowerSegment.join cell1613273344 cell1613404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1613535488 cell1613666560)
                  (ThetaLowerSegment.join cell1613797632 cell1613928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1614059776 cell1614190848)
                  (ThetaLowerSegment.join cell1614321920 cell1614452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1614584064 cell1614715136)
                  (ThetaLowerSegment.join cell1614846208 cell1614977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1615108352 cell1615239424)
                  (ThetaLowerSegment.join cell1615370496 cell1615501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1615632640 cell1615763712)
                  (ThetaLowerSegment.join cell1615894784 cell1616025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1616156928 cell1616288000)
                  (ThetaLowerSegment.join cell1616419072 cell1616550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1616681216 cell1616812288)
                  (ThetaLowerSegment.join cell1616943360 cell1617074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1617205504 cell1617336576)
                  (ThetaLowerSegment.join cell1617467648 cell1617598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1617729792 cell1617860864)
                  (ThetaLowerSegment.join cell1617991936 cell1618123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1618254080 cell1618385152)
                  (ThetaLowerSegment.join cell1618516224 cell1618647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1618778368 cell1618909440)
                  (ThetaLowerSegment.join cell1619040512 cell1619171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1619302656 cell1619433728)
                  (ThetaLowerSegment.join cell1619564800 cell1619695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1619826944 cell1619958016)
                  (ThetaLowerSegment.join cell1620089088 cell1620220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1620351232 cell1620482304)
                  (ThetaLowerSegment.join cell1620613376 cell1620744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1620875520 cell1621006592)
                  (ThetaLowerSegment.join cell1621137664 cell1621268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1621399808 cell1621530880)
                  (ThetaLowerSegment.join cell1621661952 cell1621793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1621924096 cell1622055168)
                  (ThetaLowerSegment.join cell1622186240 cell1622317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1622448384 cell1622579456)
                  (ThetaLowerSegment.join cell1622710528 cell1622841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1622972672 cell1623103744)
                  (ThetaLowerSegment.join cell1623234816 cell1623365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1623496960 cell1623628032)
                  (ThetaLowerSegment.join cell1623759104 cell1623890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1624021248 cell1624152320)
                  (ThetaLowerSegment.join cell1624283392 cell1624414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1624545536 cell1624676608)
                  (ThetaLowerSegment.join cell1624807680 cell1624938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1625069824 cell1625200896)
                  (ThetaLowerSegment.join cell1625331968 cell1625463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1625594112 cell1625725184)
                  (ThetaLowerSegment.join cell1625856256 cell1625987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1626118400 cell1626249472)
                  (ThetaLowerSegment.join cell1626380544 cell1626511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1626642688 cell1626773760)
                  (ThetaLowerSegment.join cell1626904832 cell1627035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1627166976 cell1627298048)
                  (ThetaLowerSegment.join cell1627429120 cell1627560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1627691264 cell1627822336)
                  (ThetaLowerSegment.join cell1627953408 cell1628084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1628215552 cell1628346624)
                  (ThetaLowerSegment.join cell1628477696 cell1628608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1628739840 cell1628870912)
                  (ThetaLowerSegment.join cell1629001984 cell1629133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1629264128 cell1629395200)
                  (ThetaLowerSegment.join cell1629526272 cell1629657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1629788416 cell1629919488)
                  (ThetaLowerSegment.join cell1630050560 cell1630181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1630312704 cell1630443776)
                  (ThetaLowerSegment.join cell1630574848 cell1630705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1630836992 cell1630968064)
                  (ThetaLowerSegment.join cell1631099136 cell1631230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1631361280 cell1631492352)
                  (ThetaLowerSegment.join cell1631623424 cell1631754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1631885568 cell1632016640)
                  (ThetaLowerSegment.join cell1632147712 cell1632278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1632409856 cell1632540928)
                  (ThetaLowerSegment.join cell1632672000 cell1632803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1632934144 cell1633065216)
                  (ThetaLowerSegment.join cell1633196288 cell1633327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1633458432 cell1633589504)
                  (ThetaLowerSegment.join cell1633720576 cell1633851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1633982720 cell1634113792)
                  (ThetaLowerSegment.join cell1634244864 cell1634375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1634507008 cell1634638080)
                  (ThetaLowerSegment.join cell1634769152 cell1634900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1635031296 cell1635162368)
                  (ThetaLowerSegment.join cell1635293440 cell1635424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1635555584 cell1635686656)
                  (ThetaLowerSegment.join cell1635817728 cell1635948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1636079872 cell1636210944)
                  (ThetaLowerSegment.join cell1636342016 cell1636473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1636604160 cell1636735232)
                  (ThetaLowerSegment.join cell1636866304 cell1636997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1637128448 cell1637259520)
                  (ThetaLowerSegment.join cell1637390592 cell1637521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1637652736 cell1637783808)
                  (ThetaLowerSegment.join cell1637914880 cell1638045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1638177024 cell1638308096)
                  (ThetaLowerSegment.join cell1638439168 cell1638570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1638701312 cell1638832384)
                  (ThetaLowerSegment.join cell1638963456 cell1639094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1639225600 cell1639356672)
                  (ThetaLowerSegment.join cell1639487744 cell1639618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1639749888 cell1639880960)
                  (ThetaLowerSegment.join cell1640012032 cell1640143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1640274176 cell1640405248)
                  (ThetaLowerSegment.join cell1640536320 cell1640667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1640798464 cell1640929536)
                (ThetaLowerSegment.join cell1641060608 cell1641191680))
              (ThetaLowerSegment.join cell1641322752 cell1641339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
