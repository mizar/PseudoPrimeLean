/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 3369341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell3337341184 :
    ThetaLowerSegment 3337341184 3337472256 (66745235275003 / 20000)
      (333739285190469 / 100000) := by
  exact
    packedTile65536 3337341184 3337472256 14 5978 57769 32 _ _ (2192843 / 100000) (1096423 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3337472256 :
    ThetaLowerSegment 3337472256 3337603328 (333739285190469 / 100000)
      (333752573837229 / 100000) := by
  exact
    packedTile65536 3337472256 3337603328 14 6060 57770 32 _ _ (1096423 / 50000) (2192849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3337603328 :
    ThetaLowerSegment 3337603328 3337734400 (333752573837229 / 100000)
      (333765437095329 / 100000) := by
  exact
    packedTile65536 3337603328 3337734400 14 5866 57771 32 _ _ (43857 / 2000) (2192853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3337734400 :
    ThetaLowerSegment 3337734400 3337865472 (333765437095329 / 100000)
      (333778675354927 / 100000) := by
  exact
    packedTile65536 3337734400 3337865472 14 6037 57773 32 _ _ (1096427 / 50000) (2192857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3337865472 :
    ThetaLowerSegment 3337865472 3337996544 (333778675354927 / 100000)
      (333791904867241 / 100000) := by
  exact
    packedTile65536 3337865472 3337996544 14 6033 57774 32 _ _ (1096429 / 50000) (2192861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3337996544 :
    ThetaLowerSegment 3337996544 3338127616 (333791904867241 / 100000)
      (333804943624693 / 100000) := by
  exact
    packedTile65536 3337996544 3338127616 14 5946 57775 32 _ _ (1096431 / 50000) (438573 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3338127616 :
    ThetaLowerSegment 3338127616 3338258688 (333804943624693 / 100000)
      (333817960477269 / 100000) := by
  exact
    packedTile65536 3338127616 3338258688 14 5936 57776 32 _ _ (1096433 / 50000) (2192869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3338258688 :
    ThetaLowerSegment 3338258688 3338389760 (333817960477269 / 100000)
      (333831275583909 / 100000) := by
  exact
    packedTile65536 3338258688 3338389760 14 6072 57777 32 _ _ (219287 / 10000) (2192873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3338389760 :
    ThetaLowerSegment 3338389760 3338520832 (333831275583909 / 100000)
      (66768875162637 / 20000) := by
  exact
    packedTile65536 3338389760 3338520832 14 5974 57778 32 _ _ (1096437 / 50000) (2192877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3338520832 :
    ThetaLowerSegment 3338520832 3338651904 (66768875162637 / 20000)
      (333857370808213 / 100000) := by
  exact
    packedTile65536 3338520832 3338651904 14 5926 57779 32 _ _ (1096439 / 50000) (2192881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3338651904 :
    ThetaLowerSegment 3338651904 3338782976 (333857370808213 / 100000)
      (333870361441181 / 100000) := by
  exact
    packedTile65536 3338651904 3338782976 14 5924 57781 32 _ _ (1096441 / 50000) (438577 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3338782976 :
    ThetaLowerSegment 3338782976 3338914048 (333870361441181 / 100000)
      (333883244646431 / 100000) := by
  exact
    packedTile65536 3338782976 3338914048 14 5875 57782 32 _ _ (1096443 / 50000) (2192889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3338914048 :
    ThetaLowerSegment 3338914048 3339045120 (333883244646431 / 100000)
      (333896476544691 / 100000) := by
  exact
    packedTile65536 3338914048 3339045120 14 6034 57783 32 _ _ (219289 / 10000) (2192893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3339045120 :
    ThetaLowerSegment 3339045120 3339176192 (333896476544691 / 100000)
      (333909618558433 / 100000) := by
  exact
    packedTile65536 3339045120 3339176192 14 5993 57784 32 _ _ (1096447 / 50000) (2192897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3339176192 :
    ThetaLowerSegment 3339176192 3339307264 (333909618558433 / 100000)
      (166961327665549 / 50000) := by
  exact
    packedTile65536 3339176192 3339307264 14 5945 57785 32 _ _ (2192897 / 100000) (21929 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3339307264 :
    ThetaLowerSegment 3339307264 3339438336 (166961327665549 / 50000)
      (333935582482493 / 100000) := by
  exact
    packedTile65536 3339307264 3339438336 14 5895 57786 32 _ _ (2192901 / 100000) (274113 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3339438336 :
    ThetaLowerSegment 3339438336 3339569408 (333935582482493 / 100000)
      (166974261407449 / 50000) := by
  exact
    packedTile65536 3339438336 3339569408 14 5901 57787 32 _ _ (438581 / 20000) (548227 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3339569408 :
    ThetaLowerSegment 3339569408 3339700480 (166974261407449 / 50000)
      (166980862063539 / 50000) := by
  exact
    packedTile65536 3339569408 3339700480 14 6020 57789 32 _ _ (2192909 / 100000) (137057 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3339700480 :
    ThetaLowerSegment 3339700480 3339831552 (166980862063539 / 50000) (66794927638347 / 20000) := by
  exact
    packedTile65536 3339700480 3339831552 14 5889 57790 32 _ _ (2192913 / 100000) (548229 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3339831552 :
    ThetaLowerSegment 3339831552 3339962624 (66794927638347 / 20000)
      (333987786922067 / 100000) := by
  exact
    packedTile65536 3339831552 3339962624 14 5996 57791 32 _ _ (2192917 / 100000) (54823 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3339962624 :
    ThetaLowerSegment 3339962624 3340093696 (333987786922067 / 100000)
      (334000869888753 / 100000) := by
  exact
    packedTile65536 3339962624 3340093696 14 5966 57792 32 _ _ (2192921 / 100000) (548231 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3340093696 :
    ThetaLowerSegment 3340093696 3340224768 (334000869888753 / 100000)
      (167007006044139 / 50000) := by
  exact
    packedTile65536 3340093696 3340224768 14 5993 57793 32 _ _ (87717 / 4000) (68529 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3340224768 :
    ThetaLowerSegment 3340224768 3340355840 (167007006044139 / 50000) (33402714334713 / 10000) := by
  exact
    packedTile65536 3340224768 3340355840 14 5988 57794 32 _ _ (2192929 / 100000) (548233 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3340355840 :
    ThetaLowerSegment 3340355840 3340486912 (33402714334713 / 10000) (167020137314967 / 50000) := by
  exact
    packedTile65536 3340355840 3340486912 14 5988 57795 32 _ _ (2192933 / 100000) (274117 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3340486912 :
    ThetaLowerSegment 3340486912 3340617984 (167020137314967 / 50000) (8351334600183 / 2500) := by
  exact
    packedTile65536 3340486912 3340617984 14 5978 57796 32 _ _ (2192937 / 100000) (109647 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3340617984 :
    ThetaLowerSegment 3340617984 3340749056 (8351334600183 / 2500) (10439581071372 / 3125) := by
  exact
    packedTile65536 3340617984 3340749056 14 6024 57798 32 _ _ (2192941 / 100000) (137059 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3340749056 :
    ThetaLowerSegment 3340749056 3340880128 (10439581071372 / 3125) (167039786066207 / 50000) := by
  exact
    packedTile65536 3340749056 3340880128 14 5918 57799 32 _ _ (438589 / 20000) (548237 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3340880128 :
    ThetaLowerSegment 3340880128 3341011200 (167039786066207 / 50000)
      (334092784650139 / 100000) := by
  exact
    packedTile65536 3340880128 3341011200 14 6025 57800 32 _ _ (2192949 / 100000) (274119 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3341011200 :
    ThetaLowerSegment 3341011200 3341142272 (334092784650139 / 100000)
      (334105909467859 / 100000) := by
  exact
    packedTile65536 3341011200 3341142272 14 5985 57801 32 _ _ (274119 / 12500) (438591 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3341142272 :
    ThetaLowerSegment 3341142272 3341273344 (334105909467859 / 100000)
      (334118843522347 / 100000) := by
  exact
    packedTile65536 3341142272 3341273344 14 5898 57802 32 _ _ (548239 / 25000) (2192959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3341273344 :
    ThetaLowerSegment 3341273344 3341404416 (334118843522347 / 100000)
      (334131933300587 / 100000) := by
  exact
    packedTile65536 3341273344 3341404416 14 5969 57803 32 _ _ (13706 / 625) (2192963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3341404416 :
    ThetaLowerSegment 3341404416 3341535488 (334131933300587 / 100000)
      (334145005558991 / 100000) := by
  exact
    packedTile65536 3341404416 3341535488 14 5961 57804 32 _ _ (548241 / 25000) (2192967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3341535488 :
    ThetaLowerSegment 3341535488 3341666560 (334145005558991 / 100000)
      (334158101963887 / 100000) := by
  exact
    packedTile65536 3341535488 3341666560 14 5972 57806 32 _ _ (274121 / 12500) (2192971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3341666560 :
    ThetaLowerSegment 3341666560 3341797632 (334158101963887 / 100000)
      (334171248831027 / 100000) := by
  exact
    packedTile65536 3341666560 3341797632 14 5995 57807 32 _ _ (548243 / 25000) (87719 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3341797632 :
    ThetaLowerSegment 3341797632 3341928704 (334171248831027 / 100000)
      (334184299231203 / 100000) := by
  exact
    packedTile65536 3341797632 3341928704 14 5951 57808 32 _ _ (137061 / 6250) (2192979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3341928704 :
    ThetaLowerSegment 3341928704 3342059776 (334184299231203 / 100000)
      (334197340883263 / 100000) := by
  exact
    packedTile65536 3341928704 3342059776 14 5947 57809 32 _ _ (109649 / 5000) (2192983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3342059776 :
    ThetaLowerSegment 3342059776 3342190848 (334197340883263 / 100000)
      (334210454927583 / 100000) := by
  exact
    packedTile65536 3342059776 3342190848 14 5980 57810 32 _ _ (274123 / 12500) (2192987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3342190848 :
    ThetaLowerSegment 3342190848 3342321920 (334210454927583 / 100000)
      (334223759785779 / 100000) := by
  exact
    packedTile65536 3342190848 3342321920 14 6067 57811 32 _ _ (548247 / 25000) (2192991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3342321920 :
    ThetaLowerSegment 3342321920 3342452992 (334223759785779 / 100000)
      (334236751070387 / 100000) := by
  exact
    packedTile65536 3342321920 3342452992 14 5924 57812 32 _ _ (68531 / 3125) (438599 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3342452992 :
    ThetaLowerSegment 3342452992 3342584064 (334236751070387 / 100000)
      (334249700711767 / 100000) := by
  exact
    packedTile65536 3342452992 3342584064 14 5905 57813 32 _ _ (548249 / 25000) (2192999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3342584064 :
    ThetaLowerSegment 3342584064 3342715136 (334249700711767 / 100000)
      (334262830202767 / 100000) := by
  exact
    packedTile65536 3342584064 3342715136 14 5987 57815 32 _ _ (2193 / 100) (2193003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3342715136 :
    ThetaLowerSegment 3342715136 3342846208 (334262830202767 / 100000)
      (334276027694821 / 100000) := by
  exact
    packedTile65536 3342715136 3342846208 14 6018 57816 32 _ _ (2193003 / 100000) (1096503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3342846208 :
    ThetaLowerSegment 3342846208 3342977280 (334276027694821 / 100000)
      (167144596157921 / 50000) := by
  exact
    packedTile65536 3342846208 3342977280 14 6003 57817 32 _ _ (2193007 / 100000) (219301 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3342977280 :
    ThetaLowerSegment 3342977280 3343108352 (167144596157921 / 50000) (66860458234109 / 20000) := by
  exact
    packedTile65536 3342977280 3343108352 14 5973 57818 32 _ _ (2193011 / 100000) (1096507 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3343108352 :
    ThetaLowerSegment 3343108352 3343239424 (66860458234109 / 20000) (33431552601607 / 10000) := by
  exact
    packedTile65536 3343108352 3343239424 14 6035 57819 32 _ _ (438603 / 20000) (1096509 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3343239424 :
    ThetaLowerSegment 3343239424 3343370496 (33431552601607 / 10000)
      (334328589830253 / 100000) := by
  exact
    packedTile65536 3343239424 3343370496 14 5957 57820 32 _ _ (2193019 / 100000) (1096511 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3343370496 :
    ThetaLowerSegment 3343370496 3343501568 (334328589830253 / 100000)
      (334341791828713 / 100000) := by
  exact
    packedTile65536 3343370496 3343501568 14 6020 57821 32 _ _ (2193023 / 100000) (1096513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3343501568 :
    ThetaLowerSegment 3343501568 3343632640 (334341791828713 / 100000)
      (167177329159061 / 50000) := by
  exact
    packedTile65536 3343501568 3343632640 14 5867 57823 32 _ _ (2193027 / 100000) (219303 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3343632640 :
    ThetaLowerSegment 3343632640 3343763712 (167177329159061 / 50000)
      (334367717817727 / 100000) := by
  exact
    packedTile65536 3343632640 3343763712 14 5955 57824 32 _ _ (2193031 / 100000) (1096517 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3343763712 :
    ThetaLowerSegment 3343763712 3343894784 (334367717817727 / 100000)
      (83595231616883 / 25000) := by
  exact
    packedTile65536 3343763712 3343894784 14 6023 57825 32 _ _ (438607 / 20000) (1096519 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3343894784 :
    ThetaLowerSegment 3343894784 3344025856 (83595231616883 / 25000) (83598503631071 / 25000) := by
  exact
    packedTile65536 3343894784 3344025856 14 5968 57826 32 _ _ (2193039 / 100000) (1096521 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3344025856 :
    ThetaLowerSegment 3344025856 3344156928 (83598503631071 / 25000) (10450223875316 / 3125) := by
  exact
    packedTile65536 3344025856 3344156928 14 5996 57827 32 _ _ (2193043 / 100000) (1096523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3344156928 :
    ThetaLowerSegment 3344156928 3344288000 (10450223875316 / 3125) (334420285010313 / 100000) := by
  exact
    packedTile65536 3344156928 3344288000 14 5983 57828 32 _ _ (2193047 / 100000) (43861 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3344288000 :
    ThetaLowerSegment 3344288000 3344419072 (334420285010313 / 100000)
      (334433256901063 / 100000) := by
  exact
    packedTile65536 3344288000 3344419072 14 5915 57829 32 _ _ (43861 / 2000) (2193053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3344419072 :
    ThetaLowerSegment 3344419072 3344550144 (334433256901063 / 100000)
      (334446296800147 / 100000) := by
  exact
    packedTile65536 3344419072 3344550144 14 5946 57830 32 _ _ (1096527 / 50000) (2193057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3344550144 :
    ThetaLowerSegment 3344550144 3344681216 (334446296800147 / 100000)
      (66891900240473 / 20000) := by
  exact
    packedTile65536 3344550144 3344681216 14 6021 57832 32 _ _ (1096529 / 50000) (2193061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3344681216 :
    ThetaLowerSegment 3344681216 3344812288 (66891900240473 / 20000)
      (334472536762893 / 100000) := by
  exact
    packedTile65536 3344681216 3344812288 14 5944 57833 32 _ _ (1096531 / 50000) (438613 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3344812288 :
    ThetaLowerSegment 3344812288 3344943360 (334472536762893 / 100000)
      (66897109206081 / 20000) := by
  exact
    packedTile65536 3344812288 3344943360 14 5932 57834 32 _ _ (1096533 / 50000) (2193069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3344943360 :
    ThetaLowerSegment 3344943360 3345074432 (66897109206081 / 20000) (66899743960379 / 20000) := by
  exact
    packedTile65536 3344943360 3345074432 14 6007 57835 32 _ _ (219307 / 10000) (2193073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3345074432 :
    ThetaLowerSegment 3345074432 3345205504 (66899743960379 / 20000)
      (334511996671891 / 100000) := by
  exact
    packedTile65536 3345074432 3345205504 14 6054 57836 32 _ _ (1096537 / 50000) (2193077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3345205504 :
    ThetaLowerSegment 3345205504 3345336576 (334511996671891 / 100000)
      (334524988465963 / 100000) := by
  exact
    packedTile65536 3345205504 3345336576 14 5924 57837 32 _ _ (1096539 / 50000) (2193081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3345336576 :
    ThetaLowerSegment 3345336576 3345467648 (334524988465963 / 100000)
      (334538326790687 / 100000) := by
  exact
    packedTile65536 3345336576 3345467648 14 6082 57838 32 _ _ (1096541 / 50000) (438617 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3345467648 :
    ThetaLowerSegment 3345467648 3345598720 (334538326790687 / 100000)
      (334551500658289 / 100000) := by
  exact
    packedTile65536 3345467648 3345598720 14 6007 57840 32 _ _ (1096543 / 50000) (2193089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3345598720 :
    ThetaLowerSegment 3345598720 3345729792 (334551500658289 / 100000)
      (334564641653569 / 100000) := by
  exact
    packedTile65536 3345598720 3345729792 14 5992 57841 32 _ _ (219309 / 10000) (2193093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3345729792 :
    ThetaLowerSegment 3345729792 3345860864 (334564641653569 / 100000)
      (334577822148509 / 100000) := by
  exact
    packedTile65536 3345729792 3345860864 14 6010 57842 32 _ _ (1096547 / 50000) (2193097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3345860864 :
    ThetaLowerSegment 3345860864 3345991936 (334577822148509 / 100000)
      (41823860255143 / 12500) := by
  exact
    packedTile65536 3345860864 3345991936 14 5955 57843 32 _ _ (2193097 / 100000) (21931 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3345991936 :
    ThetaLowerSegment 3345991936 3346123008 (41823860255143 / 12500) (167302061992491 / 50000) := by
  exact
    packedTile65536 3345991936 3346123008 14 6038 57844 32 _ _ (2193101 / 100000) (137069 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3346123008 :
    ThetaLowerSegment 3346123008 3346254080 (167302061992491 / 50000)
      (334617126904527 / 100000) := by
  exact
    packedTile65536 3346123008 3346254080 14 5929 57845 32 _ _ (438621 / 20000) (548277 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3346254080 :
    ThetaLowerSegment 3346254080 3346385152 (334617126904527 / 100000)
      (167315075889439 / 50000) := by
  exact
    packedTile65536 3346254080 3346385152 14 5939 57846 32 _ _ (2193109 / 100000) (274139 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3346385152 :
    ThetaLowerSegment 3346385152 3346516224 (167315075889439 / 50000) (33464309991803 / 10000) := by
  exact
    packedTile65536 3346385152 3346516224 14 5904 57847 32 _ _ (2193113 / 100000) (548279 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3346516224 :
    ThetaLowerSegment 3346516224 3346647296 (33464309991803 / 10000)
      (334656142384829 / 100000) := by
  exact
    packedTile65536 3346516224 3346647296 14 5947 57849 32 _ _ (2193117 / 100000) (13707 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3346647296 :
    ThetaLowerSegment 3346647296 3346778368 (334656142384829 / 100000)
      (33466925944153 / 10000) := by
  exact
    packedTile65536 3346647296 3346778368 14 5981 57850 32 _ _ (2193121 / 100000) (548281 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3346778368 :
    ThetaLowerSegment 3346778368 3346909440 (33466925944153 / 10000) (66936487585931 / 20000) := by
  exact
    packedTile65536 3346778368 3346909440 14 6009 57851 32 _ _ (3509 / 160) (274141 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3346909440 :
    ThetaLowerSegment 3346909440 3347040512 (66936487585931 / 20000)
      (334695451957141 / 100000) := by
  exact
    packedTile65536 3346909440 3347040512 14 5934 57852 32 _ _ (2193129 / 100000) (548283 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3347040512 :
    ThetaLowerSegment 3347040512 3347171584 (334695451957141 / 100000)
      (41838554138921 / 12500) := by
  exact
    packedTile65536 3347040512 3347171584 14 5919 57853 32 _ _ (2193133 / 100000) (137071 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3347171584 :
    ThetaLowerSegment 3347171584 3347302656 (41838554138921 / 12500)
      (334721576581409 / 100000) := by
  exact
    packedTile65536 3347171584 3347302656 14 5993 57854 32 _ _ (2193137 / 100000) (109657 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3347302656 :
    ThetaLowerSegment 3347302656 3347433728 (334721576581409 / 100000)
      (334734691564589 / 100000) := by
  exact
    packedTile65536 3347302656 3347433728 14 5980 57855 32 _ _ (2193141 / 100000) (274143 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3347433728 :
    ThetaLowerSegment 3347433728 3347564800 (334734691564589 / 100000)
      (334747764895973 / 100000) := by
  exact
    packedTile65536 3347433728 3347564800 14 5961 57857 32 _ _ (274143 / 12500) (2193147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3347564800 :
    ThetaLowerSegment 3347564800 3347695872 (334747764895973 / 100000)
      (334760739559541 / 100000) := by
  exact
    packedTile65536 3347564800 3347695872 14 5916 57858 32 _ _ (548287 / 25000) (2193151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3347695872 :
    ThetaLowerSegment 3347695872 3347826944 (334760739559541 / 100000)
      (334773817324917 / 100000) := by
  exact
    packedTile65536 3347695872 3347826944 14 5963 57859 32 _ _ (68536 / 3125) (438631 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3347826944 :
    ThetaLowerSegment 3347826944 3347958016 (334773817324917 / 100000)
      (334786897307301 / 100000) := by
  exact
    packedTile65536 3347826944 3347958016 14 5964 57860 32 _ _ (548289 / 25000) (2193159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3347958016 :
    ThetaLowerSegment 3347958016 3348089088 (334786897307301 / 100000)
      (334799988279341 / 100000) := by
  exact
    packedTile65536 3347958016 3348089088 14 5969 57861 32 _ _ (54829 / 2500) (2193163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3348089088 :
    ThetaLowerSegment 3348089088 3348220160 (334799988279341 / 100000)
      (66962616732317 / 20000) := by
  exact
    packedTile65536 3348089088 3348220160 14 5971 57862 32 _ _ (548291 / 25000) (2193167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3348220160 :
    ThetaLowerSegment 3348220160 3348351232 (66962616732317 / 20000)
      (334826172488209 / 100000) := by
  exact
    packedTile65536 3348220160 3348351232 14 5968 57863 32 _ _ (137073 / 6250) (2193171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3348351232 :
    ThetaLowerSegment 3348351232 3348482304 (334826172488209 / 100000)
      (334839210895749 / 100000) := by
  exact
    packedTile65536 3348351232 3348482304 14 5945 57864 32 _ _ (548293 / 25000) (87727 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3348482304 :
    ThetaLowerSegment 3348482304 3348613376 (334839210895749 / 100000)
      (334852541019477 / 100000) := by
  exact
    packedTile65536 3348482304 3348613376 14 6078 57866 32 _ _ (274147 / 12500) (2193179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3348613376 :
    ThetaLowerSegment 3348613376 3348744448 (334852541019477 / 100000)
      (334865557542777 / 100000) := by
  exact
    packedTile65536 3348613376 3348744448 14 5935 57867 32 _ _ (109659 / 5000) (2193183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3348744448 :
    ThetaLowerSegment 3348744448 3348875520 (334865557542777 / 100000)
      (334878804374137 / 100000) := by
  exact
    packedTile65536 3348744448 3348875520 14 6040 57868 32 _ _ (68537 / 3125) (2193187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3348875520 :
    ThetaLowerSegment 3348875520 3349006592 (334878804374137 / 100000)
      (334891869195053 / 100000) := by
  exact
    packedTile65536 3348875520 3349006592 14 5957 57869 32 _ _ (548297 / 25000) (2193191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3349006592 :
    ThetaLowerSegment 3349006592 3349137664 (334891869195053 / 100000)
      (83726257633561 / 25000) := by
  exact
    packedTile65536 3349006592 3349137664 14 6001 57870 32 _ _ (2193191 / 100000) (1096597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3349137664 :
    ThetaLowerSegment 3349137664 3349268736 (83726257633561 / 25000)
      (334918126101589 / 100000) := by
  exact
    packedTile65536 3349137664 3349268736 14 5971 57871 32 _ _ (438639 / 20000) (1096599 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3349268736 :
    ThetaLowerSegment 3349268736 3349399808 (334918126101589 / 100000)
      (83732747303431 / 25000) := by
  exact
    packedTile65536 3349268736 3349399808 14 5865 57872 32 _ _ (2193199 / 100000) (1096601 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3349399808 :
    ThetaLowerSegment 3349399808 3349530880 (83732747303431 / 25000)
      (334944233966641 / 100000) := by
  exact
    packedTile65536 3349399808 3349530880 14 6039 57873 32 _ _ (2193203 / 100000) (1096603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3349530880 :
    ThetaLowerSegment 3349530880 3349661952 (334944233966641 / 100000)
      (83739364202911 / 25000) := by
  exact
    packedTile65536 3349530880 3349661952 14 6029 57875 32 _ _ (2193207 / 100000) (219321 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3349661952 :
    ThetaLowerSegment 3349661952 3349793024 (83739364202911 / 25000) (418713259131 / 125) := by
  exact
    packedTile65536 3349661952 3349793024 14 5996 57876 32 _ _ (2193211 / 100000) (1096607 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3349793024 :
    ThetaLowerSegment 3349793024 3349924096 (418713259131 / 125) (66996779198897 / 20000) := by
  exact
    packedTile65536 3349793024 3349924096 14 6059 57877 32 _ _ (438643 / 20000) (1096609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3349924096 :
    ThetaLowerSegment 3349924096 3350055168 (66996779198897 / 20000) (41874623414837 / 12500) := by
  exact
    packedTile65536 3349924096 3350055168 14 5969 57878 32 _ _ (2193219 / 100000) (1096611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3350055168 :
    ThetaLowerSegment 3350055168 3350186240 (41874623414837 / 12500) (83752525698059 / 25000) := by
  exact
    packedTile65536 3350055168 3350186240 14 5980 57879 32 _ _ (2193223 / 100000) (1096613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3350186240 :
    ThetaLowerSegment 3350186240 3350317312 (83752525698059 / 25000)
      (335023106435119 / 100000) := by
  exact
    packedTile65536 3350186240 3350317312 14 5929 57880 32 _ _ (2193227 / 100000) (219323 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3350317312 :
    ThetaLowerSegment 3350317312 3350448384 (335023106435119 / 100000)
      (83759068100203 / 25000) := by
  exact
    packedTile65536 3350317312 3350448384 14 6003 57881 32 _ _ (2193231 / 100000) (1096617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3350448384 :
    ThetaLowerSegment 3350448384 3350579456 (83759068100203 / 25000) (167524761963341 / 50000) := by
  exact
    packedTile65536 3350448384 3350579456 14 6042 57883 32 _ _ (438647 / 20000) (1096619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3350579456 :
    ThetaLowerSegment 3350579456 3350710528 (167524761963341 / 50000) (33506256491983 / 10000) := by
  exact
    packedTile65536 3350579456 3350710528 14 5946 57884 32 _ _ (1096619 / 50000) (2193241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3350710528 :
    ThetaLowerSegment 3350710528 3350841600 (33506256491983 / 10000) (83768897646017 / 25000) := by
  exact
    packedTile65536 3350710528 3350841600 14 5939 57885 32 _ _ (1096621 / 50000) (438649 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3350841600 :
    ThetaLowerSegment 3350841600 3350972672 (83768897646017 / 25000) (41886080049721 / 12500) := by
  exact
    packedTile65536 3350841600 3350972672 14 5950 57886 32 _ _ (1096623 / 50000) (2193249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3350972672 :
    ThetaLowerSegment 3350972672 3351103744 (41886080049721 / 12500) (83775444491317 / 25000) := by
  exact
    packedTile65536 3350972672 3351103744 14 5990 57887 32 _ _ (8773 / 400) (2193253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3351103744 :
    ThetaLowerSegment 3351103744 3351234816 (83775444491317 / 25000) (167557542218643 / 50000) := by
  exact
    packedTile65536 3351103744 3351234816 14 6067 57888 32 _ _ (1096627 / 50000) (2193257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3351234816 :
    ThetaLowerSegment 3351234816 3351365888 (167557542218643 / 50000) (83782049481717 / 25000) := by
  exact
    packedTile65536 3351234816 3351365888 14 5979 57889 32 _ _ (1096629 / 50000) (2193261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3351365888 :
    ThetaLowerSegment 3351365888 3351496960 (83782049481717 / 25000) (33514131582689 / 10000) := by
  exact
    packedTile65536 3351365888 3351496960 14 5981 57890 32 _ _ (1096631 / 50000) (438653 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3351496960 :
    ThetaLowerSegment 3351496960 3351628032 (33514131582689 / 10000) (167577268417169 / 50000) := by
  exact
    packedTile65536 3351496960 3351628032 14 6028 57892 32 _ _ (1096633 / 50000) (2193269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3351628032 :
    ThetaLowerSegment 3351628032 3351759104 (167577268417169 / 50000)
      (167583797781959 / 50000) := by
  exact
    packedTile65536 3351628032 3351759104 14 5954 57893 32 _ _ (219327 / 10000) (2193273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3351759104 :
    ThetaLowerSegment 3351759104 3351890176 (167583797781959 / 50000)
      (167590281099903 / 50000) := by
  exact
    packedTile65536 3351759104 3351890176 14 5912 57894 32 _ _ (1096637 / 50000) (2193277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3351890176 :
    ThetaLowerSegment 3351890176 3352021248 (167590281099903 / 50000) (83798376183321 / 25000) := by
  exact
    packedTile65536 3351890176 3352021248 14 5901 57895 32 _ _ (1096639 / 50000) (2193281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3352021248 :
    ThetaLowerSegment 3352021248 3352152320 (83798376183321 / 25000) (83801635398887 / 25000) := by
  exact
    packedTile65536 3352021248 3352152320 14 5944 57896 32 _ _ (2193281 / 100000) (548321 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3352152320 :
    ThetaLowerSegment 3352152320 3352283392 (83801635398887 / 25000) (167609791434079 / 50000) := by
  exact
    packedTile65536 3352152320 3352283392 14 5946 57897 32 _ _ (438657 / 20000) (274161 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3352283392 :
    ThetaLowerSegment 3352283392 3352414464 (167609791434079 / 50000)
      (167616283569519 / 50000) := by
  exact
    packedTile65536 3352283392 3352414464 14 5920 57898 32 _ _ (2193289 / 100000) (548323 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3352414464 :
    ThetaLowerSegment 3352414464 3352545536 (167616283569519 / 50000)
      (335245720317159 / 100000) := by
  exact
    packedTile65536 3352414464 3352545536 14 5997 57900 32 _ _ (2193293 / 100000) (137081 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3352545536 :
    ThetaLowerSegment 3352545536 3352676608 (335245720317159 / 100000)
      (335258972217633 / 100000) := by
  exact
    packedTile65536 3352545536 3352676608 14 6042 57901 32 _ _ (2193297 / 100000) (21933 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3352676608 :
    ThetaLowerSegment 3352676608 3352807680 (335258972217633 / 100000)
      (83818041230787 / 25000) := by
  exact
    packedTile65536 3352676608 3352807680 14 6015 57902 32 _ _ (2193301 / 100000) (274163 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3352807680 :
    ThetaLowerSegment 3352807680 3352938752 (83818041230787 / 25000) (41910646951051 / 12500) := by
  exact
    packedTile65536 3352807680 3352938752 14 5932 57903 32 _ _ (438661 / 20000) (548327 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3352938752 :
    ThetaLowerSegment 3352938752 3353069824 (41910646951051 / 12500)
      (335298416614841 / 100000) := by
  exact
    packedTile65536 3352938752 3353069824 14 6037 57904 32 _ _ (2193309 / 100000) (68541 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3353069824 :
    ThetaLowerSegment 3353069824 3353200896 (335298416614841 / 100000)
      (335311387867923 / 100000) := by
  exact
    packedTile65536 3353069824 3353200896 14 5914 57905 32 _ _ (2193313 / 100000) (548329 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3353200896 :
    ThetaLowerSegment 3353200896 3353331968 (335311387867923 / 100000)
      (83831166003931 / 25000) := by
  exact
    packedTile65536 3353200896 3353331968 14 6053 57906 32 _ _ (2193317 / 100000) (54833 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3353331968 :
    ThetaLowerSegment 3353331968 3353463040 (83831166003931 / 25000)
      (335337786655267 / 100000) := by
  exact
    packedTile65536 3353331968 3353463040 14 5983 57907 32 _ _ (2193321 / 100000) (548331 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3353463040 :
    ThetaLowerSegment 3353463040 3353594112 (335337786655267 / 100000)
      (335350964145859 / 100000) := by
  exact
    packedTile65536 3353463040 3353594112 14 6008 57909 32 _ _ (548331 / 25000) (2193327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3353594112 :
    ThetaLowerSegment 3353594112 3353725184 (335350964145859 / 100000)
      (335364075860643 / 100000) := by
  exact
    packedTile65536 3353594112 3353725184 14 5978 57910 32 _ _ (137083 / 6250) (2193331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3353725184 :
    ThetaLowerSegment 3353725184 3353856256 (335364075860643 / 100000)
      (335377202952663 / 100000) := by
  exact
    packedTile65536 3353725184 3353856256 14 5985 57911 32 _ _ (548333 / 25000) (438667 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3353856256 :
    ThetaLowerSegment 3353856256 3353987328 (335377202952663 / 100000)
      (335390347615311 / 100000) := by
  exact
    packedTile65536 3353856256 3353987328 14 5993 57912 32 _ _ (274167 / 12500) (2193339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3353987328 :
    ThetaLowerSegment 3353987328 3354118400 (335390347615311 / 100000)
      (335403327801431 / 100000) := by
  exact
    packedTile65536 3353987328 3354118400 14 5918 57913 32 _ _ (109667 / 5000) (2193343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3354118400 :
    ThetaLowerSegment 3354118400 3354249472 (335403327801431 / 100000)
      (335416459351959 / 100000) := by
  exact
    packedTile65536 3354118400 3354249472 14 5987 57914 32 _ _ (68542 / 3125) (2193347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3354249472 :
    ThetaLowerSegment 3354249472 3354380544 (335416459351959 / 100000)
      (335429522932647 / 100000) := by
  exact
    packedTile65536 3354249472 3354380544 14 5956 57915 32 _ _ (548337 / 25000) (2193351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3354380544 :
    ThetaLowerSegment 3354380544 3354511616 (335429522932647 / 100000) (2683542148683 / 800) := by
  exact
    packedTile65536 3354380544 3354511616 14 6039 57917 32 _ _ (274169 / 12500) (438671 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3354511616 :
    ThetaLowerSegment 3354511616 3354642688 (2683542148683 / 800) (335455944074867 / 100000) := by
  exact
    packedTile65536 3354511616 3354642688 14 6007 57918 32 _ _ (548339 / 25000) (2193359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3354642688 :
    ThetaLowerSegment 3354642688 3354773760 (335455944074867 / 100000)
      (335469161262227 / 100000) := by
  exact
    packedTile65536 3354642688 3354773760 14 6026 57919 32 _ _ (27417 / 1250) (2193363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3354773760 :
    ThetaLowerSegment 3354773760 3354904832 (335469161262227 / 100000)
      (67096427879403 / 20000) := by
  exact
    packedTile65536 3354773760 3354904832 14 5917 57920 32 _ _ (548341 / 25000) (2193367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3354904832 :
    ThetaLowerSegment 3354904832 3355035904 (67096427879403 / 20000)
      (335495137289857 / 100000) := by
  exact
    packedTile65536 3354904832 3355035904 14 5926 57921 32 _ _ (2193367 / 100000) (219337 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3355035904 :
    ThetaLowerSegment 3355035904 3355166976 (335495137289857 / 100000) (8387701570629 / 2500) := by
  exact
    packedTile65536 3355035904 3355166976 14 5893 57922 32 _ _ (2193371 / 100000) (1096687 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3355166976 :
    ThetaLowerSegment 3355166976 3355298048 (8387701570629 / 2500) (67104188025957 / 20000) := by
  exact
    packedTile65536 3355166976 3355298048 14 5871 57923 32 _ _ (17547 / 800) (1096689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3355298048 :
    ThetaLowerSegment 3355298048 3355429120 (67104188025957 / 20000) (167767097359541 / 50000) := by
  exact
    packedTile65536 3355298048 3355429120 14 6043 57924 32 _ _ (2193379 / 100000) (1096691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3355429120 :
    ThetaLowerSegment 3355429120 3355560192 (167767097359541 / 50000) (41943406765183 / 12500) := by
  exact
    packedTile65536 3355429120 3355560192 14 5954 57926 32 _ _ (2193383 / 100000) (1096693 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3355560192 :
    ThetaLowerSegment 3355560192 3355691264 (41943406765183 / 12500)
      (335560385929433 / 100000) := by
  exact
    packedTile65536 3355560192 3355691264 14 5987 57927 32 _ _ (2193387 / 100000) (219339 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3355691264 :
    ThetaLowerSegment 3355691264 3355822336 (335560385929433 / 100000)
      (67114701358879 / 20000) := by
  exact
    packedTile65536 3355691264 3355822336 14 5982 57928 32 _ _ (2193391 / 100000) (1096697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3355822336 :
    ThetaLowerSegment 3355822336 3355953408 (67114701358879 / 20000) (13423466160161 / 4000) := by
  exact
    packedTile65536 3355822336 3355953408 14 5994 57929 32 _ _ (438679 / 20000) (1096699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3355953408 :
    ThetaLowerSegment 3355953408 3356084480 (13423466160161 / 4000) (67119949719211 / 20000) := by
  exact
    packedTile65536 3355953408 3356084480 14 5970 57930 32 _ _ (2193399 / 100000) (1096701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3356084480 :
    ThetaLowerSegment 3356084480 3356215552 (67119949719211 / 20000)
      (335612566843187 / 100000) := by
  exact
    packedTile65536 3356084480 3356215552 14 5844 57931 32 _ _ (2193403 / 100000) (1096703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3356215552 :
    ThetaLowerSegment 3356215552 3356346624 (335612566843187 / 100000)
      (335625545226489 / 100000) := by
  exact
    packedTile65536 3356215552 3356346624 14 5917 57932 32 _ _ (1096703 / 50000) (2193409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3356346624 :
    ThetaLowerSegment 3356346624 3356477696 (335625545226489 / 100000)
      (335638429316829 / 100000) := by
  exact
    packedTile65536 3356346624 3356477696 14 5874 57933 32 _ _ (219341 / 10000) (2193413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3356477696 :
    ThetaLowerSegment 3356477696 3356608768 (335638429316829 / 100000)
      (335651372652843 / 100000) := by
  exact
    packedTile65536 3356477696 3356608768 14 5901 57935 32 _ _ (1096707 / 50000) (2193417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3356608768 :
    ThetaLowerSegment 3356608768 3356739840 (335651372652843 / 100000)
      (335664550708187 / 100000) := by
  exact
    packedTile65536 3356608768 3356739840 14 6008 57936 32 _ _ (1096709 / 50000) (2193421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3356739840 :
    ThetaLowerSegment 3356739840 3356870912 (335664550708187 / 100000)
      (335677627890151 / 100000) := by
  exact
    packedTile65536 3356739840 3356870912 14 5962 57937 32 _ _ (1096711 / 50000) (87737 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3356870912 :
    ThetaLowerSegment 3356870912 3357001984 (335677627890151 / 100000)
      (67138166024249 / 20000) := by
  exact
    packedTile65536 3356870912 3357001984 14 6019 57938 32 _ _ (1096713 / 50000) (2193429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3357001984 :
    ThetaLowerSegment 3357001984 3357133056 (67138166024249 / 20000) (67140786734413 / 20000) := by
  exact
    packedTile65536 3357001984 3357133056 14 5974 57939 32 _ _ (219343 / 10000) (2193433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3357133056 :
    ThetaLowerSegment 3357133056 3357264128 (67140786734413 / 20000)
      (335717133757877 / 100000) := by
  exact
    packedTile65536 3357133056 3357264128 14 6018 57940 32 _ _ (1096717 / 50000) (2193437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3357264128 :
    ThetaLowerSegment 3357264128 3357395200 (335717133757877 / 100000)
      (335730118910837 / 100000) := by
  exact
    packedTile65536 3357264128 3357395200 14 5920 57941 32 _ _ (1096719 / 50000) (2193441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3357395200 :
    ThetaLowerSegment 3357395200 3357526272 (335730118910837 / 100000)
      (335743082153057 / 100000) := by
  exact
    packedTile65536 3357395200 3357526272 14 5910 57943 32 _ _ (1096721 / 50000) (438689 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3357526272 :
    ThetaLowerSegment 3357526272 3357657344 (335743082153057 / 100000)
      (335756269150409 / 100000) := by
  exact
    packedTile65536 3357526272 3357657344 14 6012 57944 32 _ _ (1096723 / 50000) (2193449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3357657344 :
    ThetaLowerSegment 3357657344 3357788416 (335756269150409 / 100000)
      (335769377201633 / 100000) := by
  exact
    packedTile65536 3357657344 3357788416 14 5976 57945 32 _ _ (2193449 / 100000) (548363 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3357788416 :
    ThetaLowerSegment 3357788416 3357919488 (335769377201633 / 100000)
      (41972826836311 / 12500) := by
  exact
    packedTile65536 3357788416 3357919488 14 6035 57946 32 _ _ (2193453 / 100000) (137091 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3357919488 :
    ThetaLowerSegment 3357919488 3358050560 (41972826836311 / 12500)
      (335795650405439 / 100000) := by
  exact
    packedTile65536 3357919488 3358050560 14 5943 57947 32 _ _ (2193457 / 100000) (109673 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3358050560 :
    ThetaLowerSegment 3358050560 3358181632 (335795650405439 / 100000)
      (83952172632771 / 25000) := by
  exact
    packedTile65536 3358050560 3358181632 14 5945 57948 32 _ _ (2193461 / 100000) (274183 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3358181632 :
    ThetaLowerSegment 3358181632 3358312704 (83952172632771 / 25000) (167910923467077 / 50000) := by
  exact
    packedTile65536 3358181632 3358312704 14 5998 57949 32 _ _ (438693 / 20000) (548367 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3358312704 :
    ThetaLowerSegment 3358312704 3358443776 (167910923467077 / 50000)
      (335834865172669 / 100000) := by
  exact
    packedTile65536 3358312704 3358443776 14 5935 57950 32 _ _ (2193469 / 100000) (68546 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3358443776 :
    ThetaLowerSegment 3358443776 3358574848 (335834865172669 / 100000)
      (335847828598099 / 100000) := by
  exact
    packedTile65536 3358443776 3358574848 14 5910 57952 32 _ _ (2193473 / 100000) (548369 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3358574848 :
    ThetaLowerSegment 3358574848 3358705920 (335847828598099 / 100000)
      (335860879786249 / 100000) := by
  exact
    packedTile65536 3358574848 3358705920 14 5950 57953 32 _ _ (2193477 / 100000) (54837 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3358705920 :
    ThetaLowerSegment 3358705920 3358836992 (335860879786249 / 100000)
      (67174797605741 / 20000) := by
  exact
    packedTile65536 3358705920 3358836992 14 5976 57954 32 _ _ (2193481 / 100000) (548371 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3358836992 :
    ThetaLowerSegment 3358836992 3358968064 (67174797605741 / 20000) (13435479991269 / 4000) := by
  exact
    packedTile65536 3358836992 3358968064 14 5932 57955 32 _ _ (438697 / 20000) (137093 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3358968064 :
    ThetaLowerSegment 3358968064 3359099136 (13435479991269 / 4000) (335900081744157 / 100000) := by
  exact
    packedTile65536 3358968064 3359099136 14 5964 57956 32 _ _ (137093 / 6250) (2193491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3359099136 :
    ThetaLowerSegment 3359099136 3359230208 (335900081744157 / 100000)
      (335913222954729 / 100000) := by
  exact
    packedTile65536 3359099136 3359230208 14 5991 57957 32 _ _ (548373 / 25000) (438699 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3359230208 :
    ThetaLowerSegment 3359230208 3359361280 (335913222954729 / 100000)
      (335926239159993 / 100000) := by
  exact
    packedTile65536 3359230208 3359361280 14 5934 57958 32 _ _ (274187 / 12500) (2193499 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3359361280 :
    ThetaLowerSegment 3359361280 3359492352 (335926239159993 / 100000)
      (335939419901493 / 100000) := by
  exact
    packedTile65536 3359361280 3359492352 14 6009 57959 32 _ _ (4387 / 200) (2193503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3359492352 :
    ThetaLowerSegment 3359492352 3359623424 (335939419901493 / 100000)
      (335952381316629 / 100000) := by
  exact
    packedTile65536 3359492352 3359623424 14 5909 57961 32 _ _ (68547 / 3125) (2193507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3359623424 :
    ThetaLowerSegment 3359623424 3359754496 (335952381316629 / 100000)
      (335965399786609 / 100000) := by
  exact
    packedTile65536 3359623424 3359754496 14 5935 57962 32 _ _ (548377 / 25000) (2193511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3359754496 :
    ThetaLowerSegment 3359754496 3359885568 (335965399786609 / 100000)
      (67195755164557 / 20000) := by
  exact
    packedTile65536 3359754496 3359885568 14 6098 57963 32 _ _ (274189 / 12500) (438703 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3359885568 :
    ThetaLowerSegment 3359885568 3360016640 (67195755164557 / 20000) (67198369835629 / 20000) := by
  exact
    packedTile65536 3359885568 3360016640 14 5960 57964 32 _ _ (548379 / 25000) (2193519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3360016640 :
    ThetaLowerSegment 3360016640 3360147712 (67198369835629 / 20000) (67200983195357 / 20000) := by
  exact
    packedTile65536 3360016640 3360147712 14 5957 57965 32 _ _ (27419 / 1250) (2193523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3360147712 :
    ThetaLowerSegment 3360147712 3360278784 (67200983195357 / 20000)
      (336018035443829 / 100000) := by
  exact
    packedTile65536 3360147712 3360278784 14 5981 57966 32 _ _ (548381 / 25000) (2193527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3360278784 :
    ThetaLowerSegment 3360278784 3360409856 (336018035443829 / 100000)
      (336031187831721 / 100000) := by
  exact
    packedTile65536 3360278784 3360409856 14 5996 57967 32 _ _ (2193527 / 100000) (219353 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3360409856 :
    ThetaLowerSegment 3360409856 3360540928 (336031187831721 / 100000)
      (336044252502357 / 100000) := by
  exact
    packedTile65536 3360409856 3360540928 14 5956 57969 32 _ _ (2193531 / 100000) (1096767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3360540928 :
    ThetaLowerSegment 3360540928 3360672000 (336044252502357 / 100000)
      (84014375911823 / 25000) := by
  exact
    packedTile65536 3360540928 3360672000 14 6041 57970 32 _ _ (438707 / 20000) (1096769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3360672000 :
    ThetaLowerSegment 3360672000 3360803072 (84014375911823 / 25000) (168035277602171 / 50000) := by
  exact
    packedTile65536 3360672000 3360803072 14 5950 57971 32 _ _ (2193539 / 100000) (1096771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3360803072 :
    ThetaLowerSegment 3360803072 3360934144 (168035277602171 / 50000)
      (336083622139993 / 100000) := by
  exact
    packedTile65536 3360803072 3360934144 14 5957 57972 32 _ _ (2193543 / 100000) (1096773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3360934144 :
    ThetaLowerSegment 3360934144 3361065216 (336083622139993 / 100000)
      (168048408162599 / 50000) := by
  exact
    packedTile65536 3360934144 3361065216 14 6015 57973 32 _ _ (2193547 / 100000) (43871 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3361065216 :
    ThetaLowerSegment 3361065216 3361196288 (168048408162599 / 50000) (67222046855333 / 20000) := by
  exact
    packedTile65536 3361065216 3361196288 14 6117 57974 32 _ _ (2193551 / 100000) (1096777 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3361196288 :
    ThetaLowerSegment 3361196288 3361327360 (67222046855333 / 20000) (33612327057403 / 10000) := by
  exact
    packedTile65536 3361196288 3361327360 14 5943 57975 32 _ _ (438711 / 20000) (1096779 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3361327360 :
    ThetaLowerSegment 3361327360 3361458432 (33612327057403 / 10000) (67227275417811 / 20000) := by
  exact
    packedTile65536 3361327360 3361458432 14 5975 57976 32 _ _ (2193559 / 100000) (1096781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3361458432 :
    ThetaLowerSegment 3361458432 3361589504 (67227275417811 / 20000) (42018677776027 / 12500) := by
  exact
    packedTile65536 3361458432 3361589504 14 5947 57978 32 _ _ (2193563 / 100000) (1096783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3361589504 :
    ThetaLowerSegment 3361589504 3361720576 (42018677776027 / 12500) (168081244640439 / 50000) := by
  exact
    packedTile65536 3361589504 3361720576 14 5957 57979 32 _ _ (1096783 / 50000) (2193569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3361720576 :
    ThetaLowerSegment 3361720576 3361851648 (168081244640439 / 50000)
      (168087735414069 / 50000) := by
  exact
    packedTile65536 3361720576 3361851648 14 5918 57980 32 _ _ (219357 / 10000) (2193573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3361851648 :
    ThetaLowerSegment 3361851648 3361982720 (168087735414069 / 50000) (84047135583901 / 25000) := by
  exact
    packedTile65536 3361851648 3361982720 14 5959 57981 32 _ _ (1096787 / 50000) (2193577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3361982720 :
    ThetaLowerSegment 3361982720 3362113792 (84047135583901 / 25000) (168100934160977 / 50000) := by
  exact
    packedTile65536 3361982720 3362113792 14 6075 57982 32 _ _ (1096789 / 50000) (2193581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3362113792 :
    ThetaLowerSegment 3362113792 3362244864 (168100934160977 / 50000) (42026884484897 / 12500) := by
  exact
    packedTile65536 3362113792 3362244864 14 6021 57983 32 _ _ (1096791 / 50000) (438717 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3362244864 :
    ThetaLowerSegment 3362244864 3362375936 (42026884484897 / 12500) (168114163666101 / 50000) := by
  exact
    packedTile65536 3362244864 3362375936 14 6041 57984 32 _ _ (1096793 / 50000) (2193589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3362375936 :
    ThetaLowerSegment 3362375936 3362507008 (168114163666101 / 50000) (84060397992733 / 25000) := by
  exact
    packedTile65536 3362375936 3362507008 14 6047 57985 32 _ _ (219359 / 10000) (2193593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3362507008 :
    ThetaLowerSegment 3362507008 3362638080 (84060397992733 / 25000) (84063626963101 / 25000) := by
  exact
    packedTile65536 3362507008 3362638080 14 5888 57987 32 _ _ (1096797 / 50000) (2193597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3362638080 :
    ThetaLowerSegment 3362638080 3362769152 (84063626963101 / 25000) (168133783170649 / 50000) := by
  exact
    packedTile65536 3362638080 3362769152 14 5953 57988 32 _ _ (1096799 / 50000) (2193601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3362769152 :
    ThetaLowerSegment 3362769152 3362900224 (168133783170649 / 50000)
      (168140383719067 / 50000) := by
  exact
    packedTile65536 3362769152 3362900224 14 6018 57989 32 _ _ (1096801 / 50000) (438721 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3362900224 :
    ThetaLowerSegment 3362900224 3363031296 (168140383719067 / 50000)
      (336293891776849 / 100000) := by
  exact
    packedTile65536 3362900224 3363031296 14 5983 57990 32 _ _ (438721 / 20000) (274201 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3363031296 :
    ThetaLowerSegment 3363031296 3363162368 (336293891776849 / 100000)
      (168153532199447 / 50000) := by
  exact
    packedTile65536 3363031296 3363162368 14 6005 57991 32 _ _ (2193609 / 100000) (548403 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3363162368 :
    ThetaLowerSegment 3363162368 3363293440 (168153532199447 / 50000) (67264065835341 / 20000) := by
  exact
    packedTile65536 3363162368 3363293440 14 6047 57992 32 _ _ (2193613 / 100000) (137101 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3363293440 :
    ThetaLowerSegment 3363293440 3363424512 (67264065835341 / 20000) (84083400688293 / 25000) := by
  exact
    packedTile65536 3363293440 3363424512 14 6051 57993 32 _ _ (2193617 / 100000) (109681 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3363424512 :
    ThetaLowerSegment 3363424512 3363555584 (84083400688293 / 25000)
      (336346652604501 / 100000) := by
  exact
    packedTile65536 3363424512 3363555584 14 5949 57995 32 _ _ (2193621 / 100000) (274203 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3363555584 :
    ThetaLowerSegment 3363555584 3363686656 (336346652604501 / 100000)
      (42044949099797 / 12500) := by
  exact
    packedTile65536 3363555584 3363686656 14 5899 57996 32 _ _ (17549 / 800) (548407 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3363686656 :
    ThetaLowerSegment 3363686656 3363817728 (42044949099797 / 12500)
      (336372655859071 / 100000) := by
  exact
    packedTile65536 3363686656 3363817728 14 5955 57997 32 _ _ (2193629 / 100000) (68551 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3363817728 :
    ThetaLowerSegment 3363817728 3363948800 (336372655859071 / 100000)
      (168192863859059 / 50000) := by
  exact
    packedTile65536 3363817728 3363948800 14 5959 57998 32 _ _ (2193633 / 100000) (548409 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3363948800 :
    ThetaLowerSegment 3363948800 3364079872 (168192863859059 / 50000) (67279708150367 / 20000) := by
  exact
    packedTile65536 3363948800 3364079872 14 5841 57999 32 _ _ (2193637 / 100000) (54841 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3364079872 :
    ThetaLowerSegment 3364079872 3364210944 (67279708150367 / 20000) (42051477357601 / 12500) := by
  exact
    packedTile65536 3364079872 3364210944 14 6053 58000 32 _ _ (2193641 / 100000) (548411 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3364210944 :
    ThetaLowerSegment 3364210944 3364342016 (42051477357601 / 12500) (42053111622381 / 12500) := by
  exact
    packedTile65536 3364210944 3364342016 14 5960 58001 32 _ _ (548411 / 25000) (2193647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3364342016 :
    ThetaLowerSegment 3364342016 3364473088 (42053111622381 / 12500) (42054752745291 / 12500) := by
  exact
    packedTile65536 3364342016 3364473088 14 5985 58002 32 _ _ (137103 / 6250) (2193651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3364473088 :
    ThetaLowerSegment 3364473088 3364604160 (42054752745291 / 12500) (42056373854119 / 12500) := by
  exact
    packedTile65536 3364473088 3364604160 14 5912 58004 32 _ _ (548413 / 25000) (438731 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3364604160 :
    ThetaLowerSegment 3364604160 3364735232 (42056373854119 / 12500) (42058031161227 / 12500) := by
  exact
    packedTile65536 3364604160 3364735232 14 6044 58005 32 _ _ (274207 / 12500) (2193659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3364735232 :
    ThetaLowerSegment 3364735232 3364866304 (42058031161227 / 12500) (84119318262309 / 25000) := by
  exact
    packedTile65536 3364735232 3364866304 14 5937 58006 32 _ _ (109683 / 5000) (2193663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3364866304 :
    ThetaLowerSegment 3364866304 3364997376 (84119318262309 / 25000) (84122597789989 / 25000) := by
  exact
    packedTile65536 3364866304 3364997376 14 5980 58007 32 _ _ (68552 / 3125) (2193667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3364997376 :
    ThetaLowerSegment 3364997376 3365128448 (84122597789989 / 25000) (84125894872993 / 25000) := by
  exact
    packedTile65536 3364997376 3365128448 14 6012 58008 32 _ _ (548417 / 25000) (2193671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3365128448 :
    ThetaLowerSegment 3365128448 3365259520 (84125894872993 / 25000) (84129162347437 / 25000) := by
  exact
    packedTile65536 3365128448 3365259520 14 5958 58009 32 _ _ (274209 / 12500) (87747 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3365259520 :
    ThetaLowerSegment 3365259520 3365390592 (84129162347437 / 25000) (16826491888493 / 5000) := by
  exact
    packedTile65536 3365259520 3365390592 14 6012 58010 32 _ _ (548419 / 25000) (2193679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3365390592 :
    ThetaLowerSegment 3365390592 3365521664 (16826491888493 / 5000) (336542870416799 / 100000) := by
  exact
    packedTile65536 3365390592 3365521664 14 5941 58011 32 _ _ (2193679 / 100000) (1096841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3365521664 :
    ThetaLowerSegment 3365521664 3365652736 (336542870416799 / 100000)
      (336555821921231 / 100000) := by
  exact
    packedTile65536 3365521664 3365652736 14 5904 58013 32 _ _ (2193683 / 100000) (1096843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3365652736 :
    ThetaLowerSegment 3365652736 3365783808 (336555821921231 / 100000)
      (84142225719203 / 25000) := by
  exact
    packedTile65536 3365652736 3365783808 14 5963 58014 32 _ _ (2193687 / 100000) (219369 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3365783808 :
    ThetaLowerSegment 3365783808 3365914880 (84142225719203 / 25000)
      (336581931207661 / 100000) := by
  exact
    packedTile65536 3365783808 3365914880 14 5939 58015 32 _ _ (2193691 / 100000) (1096847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3365914880 :
    ThetaLowerSegment 3365914880 3366045952 (336581931207661 / 100000)
      (84148743181109 / 25000) := by
  exact
    packedTile65536 3365914880 3366045952 14 5945 58016 32 _ _ (438739 / 20000) (1096849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3366045952 :
    ThetaLowerSegment 3366045952 3366177024 (84148743181109 / 25000) (168304056490723 / 50000) := by
  exact
    packedTile65536 3366045952 3366177024 14 5990 58017 32 _ _ (2193699 / 100000) (1096851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3366177024 :
    ThetaLowerSegment 3366177024 3366308096 (168304056490723 / 50000)
      (168310589338257 / 50000) := by
  exact
    packedTile65536 3366177024 3366308096 14 5956 58018 32 _ _ (2193703 / 100000) (1096853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3366308096 :
    ThetaLowerSegment 3366308096 3366439168 (168310589338257 / 50000)
      (336634229039457 / 100000) := by
  exact
    packedTile65536 3366308096 3366439168 14 5949 58019 32 _ _ (2193707 / 100000) (219371 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3366439168 :
    ThetaLowerSegment 3366439168 3366570240 (336634229039457 / 100000)
      (336647483441319 / 100000) := by
  exact
    packedTile65536 3366439168 3366570240 14 6042 58021 32 _ _ (2193711 / 100000) (1096857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3366570240 :
    ThetaLowerSegment 3366570240 3366701312 (336647483441319 / 100000)
      (336660571145009 / 100000) := by
  exact
    packedTile65536 3366570240 3366701312 14 5966 58022 32 _ _ (438743 / 20000) (1096859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3366701312 :
    ThetaLowerSegment 3366701312 3366832384 (336660571145009 / 100000)
      (336673823395447 / 100000) := by
  exact
    packedTile65536 3366701312 3366832384 14 6041 58023 32 _ _ (1096859 / 50000) (2193721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3366832384 :
    ThetaLowerSegment 3366832384 3366963456 (336673823395447 / 100000)
      (67337379156969 / 20000) := by
  exact
    packedTile65536 3366832384 3366963456 14 5959 58024 32 _ _ (1096861 / 50000) (87749 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3366963456 :
    ThetaLowerSegment 3366963456 3367094528 (67337379156969 / 20000)
      (336700031816133 / 100000) := by
  exact
    packedTile65536 3366963456 3367094528 14 5988 58025 32 _ _ (1096863 / 50000) (2193729 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3367094528 :
    ThetaLowerSegment 3367094528 3367225600 (336700031816133 / 100000)
      (336713045022493 / 100000) := by
  exact
    packedTile65536 3367094528 3367225600 14 5932 58026 32 _ _ (219373 / 10000) (2193733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3367225600 :
    ThetaLowerSegment 3367225600 3367356672 (336713045022493 / 100000)
      (67345212089263 / 20000) := by
  exact
    packedTile65536 3367225600 3367356672 14 5933 58027 32 _ _ (1096867 / 50000) (2193737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3367356672 :
    ThetaLowerSegment 3367356672 3367487744 (67345212089263 / 20000)
      (336739297461407 / 100000) := by
  exact
    packedTile65536 3367356672 3367487744 14 6034 58028 32 _ _ (1096869 / 50000) (2193741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3367487744 :
    ThetaLowerSegment 3367487744 3367618816 (336739297461407 / 100000)
      (336752475269601 / 100000) := by
  exact
    packedTile65536 3367487744 3367618816 14 6007 58030 32 _ _ (1096871 / 50000) (438749 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3367618816 :
    ThetaLowerSegment 3367618816 3367749888 (336752475269601 / 100000)
      (336765609226903 / 100000) := by
  exact
    packedTile65536 3367618816 3367749888 14 5987 58031 32 _ _ (1096873 / 50000) (2193749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3367749888 :
    ThetaLowerSegment 3367749888 3367880960 (336765609226903 / 100000)
      (336778688364403 / 100000) := by
  exact
    packedTile65536 3367749888 3367880960 14 5962 58032 32 _ _ (351 / 16) (2193753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3367880960 :
    ThetaLowerSegment 3367880960 3368012032 (336778688364403 / 100000)
      (33679167318841 / 10000) := by
  exact
    packedTile65536 3367880960 3368012032 14 5919 58033 32 _ _ (2193753 / 100000) (548439 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3368012032 :
    ThetaLowerSegment 3368012032 3368143104 (33679167318841 / 10000) (168402510002999 / 50000) := by
  exact
    packedTile65536 3368012032 3368143104 14 6084 58034 32 _ _ (2193757 / 100000) (13711 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3368143104 :
    ThetaLowerSegment 3368143104 3368274176 (168402510002999 / 50000)
      (336818009264879 / 100000) := by
  exact
    packedTile65536 3368143104 3368274176 14 5921 58035 32 _ _ (2193761 / 100000) (548441 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3368274176 :
    ThetaLowerSegment 3368274176 3368405248 (336818009264879 / 100000)
      (168415514630077 / 50000) := by
  exact
    packedTile65536 3368274176 3368405248 14 5935 58036 32 _ _ (438753 / 20000) (274221 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3368405248 :
    ThetaLowerSegment 3368405248 3368536320 (168415514630077 / 50000) (84211031515271 / 25000) := by
  exact
    packedTile65536 3368405248 3368536320 14 5970 58037 32 _ _ (2193769 / 100000) (548443 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3368536320 :
    ThetaLowerSegment 3368536320 3368667392 (84211031515271 / 25000)
      (336857255792489 / 100000) := by
  exact
    packedTile65536 3368536320 3368667392 14 5985 58039 32 _ _ (2193773 / 100000) (137111 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3368667392 :
    ThetaLowerSegment 3368667392 3368798464 (336857255792489 / 100000)
      (336870396516719 / 100000) := by
  exact
    packedTile65536 3368667392 3368798464 14 5990 58040 32 _ _ (2193777 / 100000) (109689 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3368798464 :
    ThetaLowerSegment 3368798464 3368929536 (336870396516719 / 100000)
      (336883431963421 / 100000) := by
  exact
    packedTile65536 3368798464 3368929536 14 5942 58041 32 _ _ (2193781 / 100000) (274223 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3368929536 :
    ThetaLowerSegment 3368929536 3369060608 (336883431963421 / 100000)
      (168448215069773 / 50000) := by
  exact
    packedTile65536 3368929536 3369060608 14 5925 58042 32 _ _ (438757 / 20000) (548447 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3369060608 :
    ThetaLowerSegment 3369060608 3369191680 (168448215069773 / 50000)
      (168454806305819 / 50000) := by
  exact
    packedTile65536 3369060608 3369191680 14 6009 58043 32 _ _ (548447 / 25000) (2193791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3369191680 :
    ThetaLowerSegment 3369191680 3369322752 (168454806305819 / 50000)
      (168461343805979 / 50000) := by
  exact
    packedTile65536 3369191680 3369322752 14 5960 58044 32 _ _ (68556 / 3125) (438759 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3369322752 :
    ThetaLowerSegment 3369322752 3369339136 (168461343805979 / 50000)
      (168462167576377 / 50000) := by
  exact
    packedTile65536 3369322752 3369339136 11 751 58045 32 _ _ (548449 / 25000) (2193799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3369339136 :
    ThetaLowerSegment 3369339136 3369341184 (168462167576377 / 50000)
      (168462259715851 / 50000) := by
  exact
    packedTile65536 3369339136 3369341184 8 84 58046 32 _ _ (2193797 / 100000) (10969 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_3337341184_3369341184 :
    ThetaLowerSegment 3337341184 3369341184 (66745235275003 / 20000) (168462259715851 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3337341184 cell3337472256)
                  (ThetaLowerSegment.join cell3337603328 cell3337734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3337865472 cell3337996544)
                  (ThetaLowerSegment.join cell3338127616 cell3338258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3338389760 cell3338520832)
                  (ThetaLowerSegment.join cell3338651904 cell3338782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3338914048 cell3339045120)
                  (ThetaLowerSegment.join cell3339176192 cell3339307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3339438336 cell3339569408)
                  (ThetaLowerSegment.join cell3339700480 cell3339831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3339962624 cell3340093696)
                  (ThetaLowerSegment.join cell3340224768 cell3340355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3340486912 cell3340617984)
                  (ThetaLowerSegment.join cell3340749056 cell3340880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3341011200 cell3341142272)
                  (ThetaLowerSegment.join cell3341273344 cell3341404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3341535488 cell3341666560)
                  (ThetaLowerSegment.join cell3341797632 cell3341928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3342059776 cell3342190848)
                  (ThetaLowerSegment.join cell3342321920 cell3342452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3342584064 cell3342715136)
                  (ThetaLowerSegment.join cell3342846208 cell3342977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3343108352 cell3343239424)
                  (ThetaLowerSegment.join cell3343370496 cell3343501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3343632640 cell3343763712)
                  (ThetaLowerSegment.join cell3343894784 cell3344025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3344156928 cell3344288000)
                  (ThetaLowerSegment.join cell3344419072 cell3344550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3344681216 cell3344812288)
                  (ThetaLowerSegment.join cell3344943360 cell3345074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3345205504 cell3345336576)
                  (ThetaLowerSegment.join cell3345467648 cell3345598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3345729792 cell3345860864)
                  (ThetaLowerSegment.join cell3345991936 cell3346123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3346254080 cell3346385152)
                  (ThetaLowerSegment.join cell3346516224 cell3346647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3346778368 cell3346909440)
                  (ThetaLowerSegment.join cell3347040512 cell3347171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3347302656 cell3347433728)
                  (ThetaLowerSegment.join cell3347564800 cell3347695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3347826944 cell3347958016)
                  (ThetaLowerSegment.join cell3348089088 cell3348220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3348351232 cell3348482304)
                  (ThetaLowerSegment.join cell3348613376 cell3348744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3348875520 cell3349006592)
                  (ThetaLowerSegment.join cell3349137664 cell3349268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3349399808 cell3349530880)
                  (ThetaLowerSegment.join cell3349661952 cell3349793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3349924096 cell3350055168)
                  (ThetaLowerSegment.join cell3350186240 cell3350317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3350448384 cell3350579456)
                  (ThetaLowerSegment.join cell3350710528 cell3350841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3350972672 cell3351103744)
                  (ThetaLowerSegment.join cell3351234816 cell3351365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3351496960 cell3351628032)
                  (ThetaLowerSegment.join cell3351759104 cell3351890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3352021248 cell3352152320)
                  (ThetaLowerSegment.join cell3352283392 cell3352414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3352545536 cell3352676608)
                  (ThetaLowerSegment.join cell3352807680 cell3352938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3353069824 cell3353200896)
                  (ThetaLowerSegment.join cell3353331968 cell3353463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3353594112 cell3353725184)
                  (ThetaLowerSegment.join cell3353856256 cell3353987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3354118400 cell3354249472)
                  (ThetaLowerSegment.join cell3354380544 cell3354511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3354642688 cell3354773760)
                  (ThetaLowerSegment.join cell3354904832 cell3355035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3355166976 cell3355298048)
                  (ThetaLowerSegment.join cell3355429120 cell3355560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3355691264 cell3355822336)
                  (ThetaLowerSegment.join cell3355953408 cell3356084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3356215552 cell3356346624)
                  (ThetaLowerSegment.join cell3356477696 cell3356608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3356739840 cell3356870912)
                  (ThetaLowerSegment.join cell3357001984 cell3357133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3357264128 cell3357395200)
                  (ThetaLowerSegment.join cell3357526272 cell3357657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3357788416 cell3357919488)
                  (ThetaLowerSegment.join cell3358050560 cell3358181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3358312704 cell3358443776)
                  (ThetaLowerSegment.join cell3358574848 cell3358705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3358836992 cell3358968064)
                  (ThetaLowerSegment.join cell3359099136 cell3359230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3359361280 cell3359492352)
                  (ThetaLowerSegment.join cell3359623424 cell3359754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3359885568 cell3360016640)
                  (ThetaLowerSegment.join cell3360147712 cell3360278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3360409856 cell3360540928)
                  (ThetaLowerSegment.join cell3360672000 cell3360803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3360934144 cell3361065216)
                  (ThetaLowerSegment.join cell3361196288 cell3361327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3361458432 cell3361589504)
                  (ThetaLowerSegment.join cell3361720576 cell3361851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3361982720 cell3362113792)
                  (ThetaLowerSegment.join cell3362244864 cell3362375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3362507008 cell3362638080)
                  (ThetaLowerSegment.join cell3362769152 cell3362900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3363031296 cell3363162368)
                  (ThetaLowerSegment.join cell3363293440 cell3363424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3363555584 cell3363686656)
                  (ThetaLowerSegment.join cell3363817728 cell3363948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3364079872 cell3364210944)
                  (ThetaLowerSegment.join cell3364342016 cell3364473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3364604160 cell3364735232)
                  (ThetaLowerSegment.join cell3364866304 cell3364997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3365128448 cell3365259520)
                  (ThetaLowerSegment.join cell3365390592 cell3365521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3365652736 cell3365783808)
                  (ThetaLowerSegment.join cell3365914880 cell3366045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3366177024 cell3366308096)
                  (ThetaLowerSegment.join cell3366439168 cell3366570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3366701312 cell3366832384)
                  (ThetaLowerSegment.join cell3366963456 cell3367094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3367225600 cell3367356672)
                  (ThetaLowerSegment.join cell3367487744 cell3367618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3367749888 cell3367880960)
                  (ThetaLowerSegment.join cell3368012032 cell3368143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3368274176 cell3368405248)
                  (ThetaLowerSegment.join cell3368536320 cell3368667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell3368798464 cell3368929536)
                (ThetaLowerSegment.join cell3369060608 cell3369191680))
              (ThetaLowerSegment.join cell3369322752 cell3369339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
