/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleSpectralRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleCompensation
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailCert
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleRowSigns
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddlePoleRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleZeroIntegral
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleScale

/-! # Certified lower Laplace charge for the middle K141 Gaussian kernel -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private def row : MiddleIntRow :=
  ⟨5481892436118615211817041920000000000000000000000000000000,
    #[0, 5481892436118615211817041920000000000000000000000000000000,
      -192237927448914514943117876990513585848320000000000000000000,
      2528359599093516611425702171928377760416857001159557120000000,
      -17926758757973518357097053415000393239121834512770662400000000,
      78628751053465227380467435600083442461132607054031880192000000,
      -230773475773139521211212222272496782475412135790297219072000000,
      476852788860471475110759759920971369334851703708038201344000000,
      -715246109282522138214319677513707623935960022332209528832000000,
      794316842748618350493445061556891496184463341405950377984000000,
      -664307612075759688097615472364312876975121426890956464128000000,
      425499738453383114644971550639133399826394598036212831027200000,
      -212123411571376120181957466105318074645904397536366779596800000,
      83515145987019210612428792702200864322959374027318445670400000,
      -26296253188630633087770007100027596838001063363436861440000000,
      6691701216308474649712231419849395232352083815530176460800000,
      -1388002478272327291249947261458208232325762367007503214080000,
      236236748888577890699733284095679046799185258952294348800000,
      -33155000751189246636410544910457360597948102977912915200000,
      3849587694132377355262904408441742363555149760889457280000,
      -370373527473454800472735427995556912404761270053677056000,
      29523194598108819422711129528732034796824351331910304000,
      -1945710142169432201239027354269009269155092449492688000,
      105557315977776082142764917858012431602182644629512000,
      -4680252008262880767389406211683024237582594871440000,
      167756298727032139758321242272430502160137634860720,
      -4783087950005901497639266431273915792150732623160,
      105909817013709890944121099795332402160682602180,
      -1755206096921321451934637724599738209296323990, 20485342268223130272165707983077763637931515,
      -150182295542548975842430613177916980212052, 520370336396474499310428033483217408536]⟩

/-- The common half-step upper ratio for decay at rate two. -/
private def ratio : ℚ :=
  367880 / 10 ^ 6

/-- The upper bound on the complete moment after translation to the left cutoff. -/
private theorem endpoint_factor :
    (∑ i ∈ Finset.range (31 + 1),
        |((row.shift 31 47 2).num i : ℚ) / (row.shift 31 47 2).den| *
          ((i.factorial : ℚ) / (2 : ℚ) ^ (i + 1))) ≤
      29285880896914086 := by
  decide +kernel

/-- The real profile used by the checked second-derivative coefficient row. -/
private noncomputable def D : Polynomial ℝ :=
  (row.poly 31).map (Rat.castHom ℝ)

/-- The complete absolute tail is bounded at the left cutoff using one shift. -/
private theorem tail_mass_le :
    (∫ t in Set.Ioi (47 / 2 : ℝ), Real.exp (-(2 : ℝ) * t) * |D.eval t|) ≤
      ((ratio ^ 47 * 29285880896914086 : ℚ) : ℝ) := by
  have hr : Real.exp (-((1 : ℚ) : ℝ)) ≤ (ratio : ℝ) :=
    middle_exp_neg_le_of_taylor 16 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have hx := middle_exp_grid_le (a := 0) (by rw [Real.exp_zero]) hr 47
  have hE :
    Real.exp (-((2 : ℚ) : ℝ) * (((47 : ℚ) / (2 : ℤ) : ℚ) : ℝ)) ≤ ((ratio ^ 47 : ℚ) : ℝ) := by
    norm_num only [zero_add, one_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast,
      Int.cast_ofNat, Rat.cast_one, Rat.cast_pow] at hx ⊢
    exact hx
  have h := row.abs_tail_le 31 47 2 (by decide) (by decide) (by decide : (0 : ℚ) < 2) hE
  dsimp only at h
  have hM :=
    h.trans
      (Rat.cast_le.mpr
        (mul_le_mul_of_nonneg_left endpoint_factor (pow_nonneg (by decide +kernel : 0 ≤ ratio) 47)))
  simpa only [D, Polynomial.eval_map, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast,
    Int.cast_ofNat] using hM

/- The physical K141 rational coefficient row. -/
private def BData : MiddleIntRow :=
  ⟨4111419327088961408862781440000000000000000000000000000000,
    #[0, 0, 0, 685236554514826901477130240000000000000000000000000000000,
      -11500943049671037007837019631907099115520000000000000000000,
      87835830023821332697345442516169906546320137543483392000000,
      -403388483208701964803165837644531845271221794047524864000000,
      1226498570828302075483918199447610150981862921147514880000000,
      -2614571656343584248257852881808438875608566633250324480000000,
      4057364584843665343125590761507900988150333152922763264000000,
      -4677810577159328609308540428783315597797686074393658982400000,
      4057038585734415068807227309916148881646169765714334515200000,
      -2680480014613451359330521871827570337439186926001958912000000,
      1368584528820837520147523167604142197040264982168152883200000,
      -547729022096918468638577043026455917805603259693476454400000,
      174059168439747370743663959963953236909731416207068948480000,
      -44404737549859485741357619915971983968751151912288422400000,
      9175424194296577527668249628681972098224676041881922560000,
      -1546224069633778338589297615097838670931938579467321600000,
      213557770377316047671708567812694618853972923475880320000,
      -24248561829497155258406843904077079379441470503968512000,
      2266123994001172842098627129781235993996273839543456000,
      -174145172871533792144854248996269238264204311720976000,
      10968449708612145041009991444244022501361981791256000,
      -562740829296893316618947546752379734017903790128000,
      23286059049297360780394973796314887040472419254320,
      -765488787048997776338153298224303459401894125720,
      19537700562013128929453395158288762030901055580,
      -373561436668145083575237955858947534333071670, 5041103221217599872537804739160091338678025,
      -42891218323831565512533195931314664664188, 173456778798824833103476011161072469512]⟩

/-- The rational K141 physical profile in the reflected logarithmic coordinate. -/
public noncomputable def middleK141Profile : Polynomial ℚ :=
  BData.poly 31

/-- The row used in the Laplace certificate is the twice-differentiated K141 profile
with the reflected rate `3/2`. -/
private theorem profile_second :
    let P := middleK141Profile.map (Rat.castHom ℝ)
    D =
      Polynomial.C ((3 / 2 : ℝ) ^ 2) * P - Polynomial.C (2 * (3 / 2 : ℝ)) * P.derivative +
        P.derivative.derivative := by
  dsimp only [D, middleK141Profile]
  have h :=
    MiddleIntRow.poly_of_secondMatches (N := 31) (a := 3) (b := 2) (p := BData) (q := row)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
  have hm := congrArg (Polynomial.map (Rat.castHom ℝ)) h
  simpa only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    ← Polynomial.derivative_map, Rat.coe_castHom, Rat.cast_mul, Rat.cast_pow, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_intCast, Int.cast_ofNat] using hm

/-- Beyond the lower cutoff, the physical K141 lower Laplace charge is at
most one millionth. The square-root factor cancels under physical rescaling. -/
public theorem middle_k141_lower_charge {x : ℝ} (hx : 20 ≤ x) :
    let P := middleK141Profile.map (Rat.castHom ℝ)
    let Q :=
      Polynomial.C ((3 / 2 : ℝ) ^ 2) * P - Polynomial.C (2 * (3 / 2 : ℝ)) * P.derivative +
        P.derivative.derivative
    (693 / 5000 : ℝ) *
        ((middleK141Norm : ℝ) * Real.exp (-(2 : ℝ) * (x + 7 / 2)) *
          Real.exp ((2 - 1 / 2 : ℝ) * x)) *
        Real.exp (x / 2) *
        (∫ t in Set.Ioi x, Real.exp (-(2 : ℝ) * t) * |Q.eval (7 / 2 + t)|) ≤
      1 / 10 ^ 6 := by
  intro P Q
  have hA :
    (∫ t in Set.Ioi (7 / 2 + 20 : ℝ), Real.exp (-(2 : ℝ) * t) * |D.eval t|) ≤
      ((ratio ^ 47 * 29285880896914086 : ℚ) : ℝ) := by
    convert tail_mass_le using 2
    norm_num only
  have hc :
    (693 / 5000 : ℝ) * (middleK141Norm : ℝ) * ((ratio ^ 47 * 29285880896914086 : ℚ) : ℝ) ≤
      1 / 10 ^ 6 := by
    have h : (693 / 5000 : ℚ) * middleK141Norm * (ratio ^ 47 * 29285880896914086) ≤ 1 / 10 ^ 6 := by
      decide +kernel
    have hh := (Rat.cast_le (K := ℝ)).mpr h
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one] using hh
  have h :=
    middle_low_physical_charge D (by norm_num only : (0 : ℝ) < 2)
      (by norm_num only : (0 : ℝ) ≤ 7 / 2 + 20) hx
      (Rat.cast_nonneg.mpr (by decide +kernel : 0 ≤ middleK141Norm)) hA hc
  rw [profile_second] at h
  exact h

/-- A single Bernstein cell bounds the finite K141 moment at the largest support. -/
private theorem upper_moment_le :
    (∫ t in (0 : ℝ)..(57 / 2), Real.exp ((1 / 2 : ℝ) * t) * |D.eval t|) ≤
      ((1600000 * 128477150186062001574 : ℚ) : ℝ) := by
  have h := row.exp_abs_cell_le 31 0 57 2 (by decide) (by decide) (by decide +kernel) (1 / 2)
  dsimp only at h
  norm_num only [max_eq_right, Rat.cast_add, Rat.cast_div, Rat.cast_intCast, Int.cast_ofNat,
    Int.cast_zero] at h
  have he :=
    middle_exp_le_of_taylor (t := 57 / 4) (U := 1600000) 40 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  have hc : row.absCellCharge 31 0 57 2 ≤ 128477150186062001574 := by decide +kernel
  have hn := row.abs_cell_nonneg 31 0 57 2 (by decide +kernel)
  have hu :=
    mul_le_mul he ((Rat.cast_le (K := ℝ)).mpr hc) (Rat.cast_nonneg.mpr hn)
      (Rat.cast_nonneg.mpr (by decide : (0 : ℚ) ≤ 1600000))
  have hu' :
    Real.exp ((1 / 2 : ℝ) * (57 / 2)) * (row.absCellCharge 31 0 57 2 : ℝ) ≤
      ((1600000 * 128477150186062001574 : ℚ) : ℝ) := by
    norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] at hu ⊢
    exact hu
  simpa only [D, Polynomial.eval_map] using
    h.trans
      (by
        norm_num only at hu' ⊢; exact hu')

/-- On the K141 cutoff interval, the inverse-square finite moment costs at
most one twentieth in physical coordinates. -/
public theorem middle_k141_upper_charge {x : ℝ} (hl : 20 ≤ x) (hr : x ≤ 25) :
    let P := middleK141Profile.map (Rat.castHom ℝ)
    let Q :=
      Polynomial.C ((3 / 2 : ℝ) ^ 2) * P - Polynomial.C (2 * (3 / 2 : ℝ)) * P.derivative +
        P.derivative.derivative
    5 / 4 *
        ((middleK141Norm : ℝ) * Real.exp (-(2 : ℝ) * (x + 7 / 2)) *
          Real.exp ((2 - 1 / 2 : ℝ) * x)) *
        Real.exp (-2 * x) *
        Real.exp ((2 - 5 / 2 : ℝ) * (7 / 2)) *
        (∫ t in (0 : ℝ)..(7 / 2 + x), Real.exp ((5 / 2 - 2 : ℝ) * t) * |Q.eval t|) ≤
      1 / 20 := by
  intro P Q
  have hA :
    (∫ t in (0 : ℝ)..(7 / 2 + 25), Real.exp ((5 / 2 - 2 : ℝ) * t) * |D.eval t|) ≤
      ((1600000 * 128477150186062001574 : ℚ) : ℝ) := by
    convert upper_moment_le using 3 <;> norm_num only
  have he : Real.exp (-(5 / 2 : ℝ) * (7 / 2 + 20)) ≤ ((778801 / 10 ^ 6 : ℚ) ^ 235 : ℚ) := by
    convert middle_exp_neg_quarters_le 235 using 2
    norm_num only
  have hc :
    (5 / 4 : ℚ) * middleK141Norm * (778801 / 10 ^ 6) ^ 235 * (1600000 * 128477150186062001574) ≤
      1 / 20 := by
    decide +kernel
  have hκ : 0 ≤ (middleK141Norm : ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  have h :=
    middle_upper_physical_charge D (C := 1 / 20) (by norm_num only : 0 ≤ (7 / 2 + 20 : ℝ)) hl hr hκ
      hA
      (by
        refine
          (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left he (mul_nonneg (by norm_num only) hκ))
                (Rat.cast_nonneg.mpr (by decide +kernel))).trans
            ?_
        simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one] using
          (Rat.cast_le (K := ℝ)).mpr hc)
  rw [profile_second] at h
  exact h

/-- The unit-cutoff logarithmic derivative of the K141 profile has
absolute value at most `23500`, checked from the first two translated coefficients. -/
public theorem middle_k141_edge_le :
    let P := middleK141Profile.map (Rat.castHom ℝ)
    let V := fun u : ℝ ↦ u ^ (3 / 2 : ℝ) * P.eval (7 / 2 - Real.log u)
    |(fun u ↦ u * deriv V u) 1| ≤ 23500 := by
  intro P V
  rw [reflected_log_edge_eval P (3 / 2) (7 / 2)]
  let q := BData.shift 31 7 2
  have h : |(3 / 2 : ℚ) * ((q.num 0 : ℚ) / q.den) - ((q.num 1 : ℚ) / q.den)| ≤ 23500 := by
    decide +kernel
  have h0 := BData.eval_eq_shift_head 31 7 2 (by decide +kernel) (by decide)
  have h1 := BData.eval_deriv_eq_shift (N := 31) (by decide) 7 2 (by decide +kernel) (by decide)
  dsimp only [q] at h
  rw [← h0, ← h1] at h
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  have he (Q : Polynomial ℚ) :
    ((Q.eval ((7 : ℤ) / (2 : ℤ) : ℚ) : ℚ) : ℝ) =
      (Q.map (Rat.castHom ℝ)).eval (((7 : ℤ) / (2 : ℤ) : ℚ) : ℝ) := by
    rw [Polynomial.eval_map]
    exact (Polynomial.eval₂_at_apply (p := Q) (Rat.castHom ℝ) _).symm
  simp only [Rat.cast_abs, Rat.cast_mul, Rat.cast_sub] at hr
  rw [he, he, ← Polynomial.derivative_map] at hr
  simpa only [P, middleK141Profile, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast,
    Int.cast_ofNat] using hr

/-- Cached rational translation of the K141 profile to the cutoff boundary. -/
private def translated : MiddleIntRow :=
  ⟨8829205774994708066835865418197893120000000000000000000000000000000,
    #[149706981814674737442734580282145616995147847586755995208345733291274572,
      431433114367091455699344028896385748962224803330675065283420920064875576,
      559258178192746964140354566896828485943843811103010001703734361058859360,
      430425505150939882106109121337640035410354770765900122413443834740123520,
      219532094985032675567115219227138744263165450919290991449182061790630720,
      79783300985498174166095964658325402603736505173336719444331137393519232,
      22484923138348151449677269632186720350407099963959054852698096250822656,
      5367800926888444530747496249076323854819822309406384631058325287244800,
      1123220780477819709985371761233241649736731548094447871122767466777600,
      241604169168605667599478259643593508052820651315241359586471396505600,
      66863748319779609019834670316750320458407979374963185832103402414080,
      10454871901346171974879520023735247196375142376233288235930213744640,
      -2378515045501683556906915223846684198734041794335977774010998374400,
      -652390185704699501974460246245171951683767615073722072969067724800,
      232025828683258776594040334527653659168152589385212075297714995200,
      53340795897732062580479026302586511027476232932705440315247165440,
      -11980487300317852099337321063076050995340112049873361416039956480,
      -1955258043447463749797715256559308908942224589604624169002598400,
      529612822661224662589370604601498058776847420985561119666995200,
      30380252931825584984708691607578958828683953069277413847859200,
      -15899883611258680062105109414536055944015352682748838328401920,
      613312878479964444612531766825630015885352927720707341680640,
      242509786851922392417576124398708617168478963785425276108800,
      -33621517857260202457649169150828883138019468174963402342400,
      349941760008874804408425276884316423044346288151304601600,
      334141619662025500466667168334034241306744566975595282432,
      -43155403086486202176692200916696799624845004516353900544,
      2906487654884961982489005411422727013644542238114447360,
      -122442875216836317189062227463277770798019799133716480,
      3276154825470578564153515464043150826017955480862720,
      -51692417815808864582800022206417827976377299632128,
      372495596105229410706043825928668622419998539776]⟩

/-- Check the cached translation once, before the weighted sum is evaluated. -/
private theorem translated_ok : (BData.shift 31 7 2).poly 31 = translated.poly 31 := by
  apply MiddleIntRow.poly_eq_of_matches (by decide +kernel) (by decide +kernel)
  decide +kernel

/-- The physical K141 principal zero series stays below its manuscript
budget for every positive cutoff under RH. -/
public theorem middle_k141_spectral_le (hRH : RiemannHypothesis) {X : ℝ} (hX : 0 < X) :
    |(middleK141Norm : ℝ) * Real.exp (-(7 : ℝ)) *
          ∑' ρ,
            principalCancelledTerm (middleK141Profile.map (Rat.castHom ℝ)) (3 / 2 : ℝ) (7 / 2) X
              ρ| ≤
      25739 / 10 ^ 6 := by
  have he :
    (middleK141Norm : ℝ) * Real.exp (-(((3 / 2 : ℚ) : ℝ) + 1 / 2) * (((7 : ℤ) / (2 : ℤ) : ℚ) : ℝ)) ≤
      (middleK141Scale : ℝ) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast, Int.cast_ofNat]
    exact middle_k141_scale_le
  have h :=
    middle_spectral_row_le BData translated 31 hRH (a := 7) (b := 2) (d := 3 / 2) (κ :=
      middleK141Norm) (E := middleK141Scale) hX (by decide +kernel) (by decide +kernel) (by decide)
      (by decide +kernel) (by decide +kernel) (by decide) (by decide) (by decide) translated_ok
      (by decide) (by decide) he
  have hc :
    (∑ j ∈ Finset.range (31 + 1),
        BData.spectralCharge translated (3 / 2) middleK141Norm middleK141Scale j) ≤
      (25739 / 10 ^ 6 : ℚ) := by
    decide +kernel
  dsimp only at h
  have hh := h.trans ((Rat.cast_le (K := ℝ)).mpr hc)
  norm_num only [middleK141Profile, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast, Int.cast_ofNat,
    Rat.cast_pow] at hh ⊢
  exact hh

/-- The K141 profile and its derivative vanish at the compact support edge. -/
public theorem middle_k141_profile_jet :
    let B := middleK141Profile.map (Rat.castHom ℝ)
    B.eval 0 = 0 ∧ B.derivative.eval 0 = 0 := by
  change
    ((BData.poly 31).map (Rat.castHom ℝ)).eval 0 = 0 ∧
      ((BData.poly 31).map (Rat.castHom ℝ)).derivative.eval 0 = 0
  have hs : BData.nums.size ≤ 31 + 1 := by decide
  have h0 : BData.num 0 = 0 := by decide
  have h1 : BData.num 1 = 0 := by decide
  constructor
  · rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map, BData.poly_coeff_all 31 hs, h0,
      Int.cast_zero, zero_div, map_zero]
  · rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative, zero_add,
      Polynomial.coeff_map, BData.poly_coeff_all 31 hs, h1, Int.cast_zero, zero_div, map_zero,
      zero_mul]

/-- The K141 principal slope uses one scalar moment at each endpoint.
The shifted moment reuses the translated row already checked for the zero series. -/
public theorem middle_k141_principal_slope :
    let M := middleMomentPoly middleK141Profile (5 / 2) 0
    (501705565937097 / 10 ^ 10 : ℚ) ≤ M.eval (7 / 2) ∧
      middleK141Norm * M.eval 0 ≤ 60099052035064 / 10 ^ 15 := by
  have he :
    (middleMomentPoly middleK141Profile (5 / 2) 0).eval (7 / 2) =
      (middleMomentPoly (translated.poly 31) (5 / 2) 0).eval 0 := by
    have h := BData.poly_shift 31 7 2 (by decide +kernel) (by decide)
    rw [translated_ok] at h
    have hm := middle_moment_translate middleK141Profile (r := 5 / 2) (by norm_num only) (7 / 2)
    have ht :
      translated.poly 31 = middleK141Profile.comp (Polynomial.X + Polynomial.C (7 / 2)) := by
      simpa only [middleK141Profile, Int.cast_ofNat] using h
    rw [← ht] at hm
    simpa only [middleMomentPoly, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, zero_add, Polynomial.C_0, add_zero, Polynomial.comp_X] using
      congrArg (fun P : Polynomial ℚ ↦ P.eval 0) hm
  dsimp only
  constructor
  · rw [he, ← show (((5 : ℤ) : ℚ) / (2 : ℤ)) = 5 / 2 from by simp only [Int.cast_ofNat],
      translated.moment_head 31 5 2 (by decide +kernel) (by decide) (by decide)]
    decide +kernel
  · change
      middleK141Norm * (middleMomentPoly (BData.poly 31) ((((5 : ℤ) : ℚ) / (2 : ℤ))) 0).eval 0 ≤ _
    rw [BData.moment_head 31 5 2 (by decide +kernel) (by decide) (by decide)]
    decide +kernel

/-- Read the K141 cutoff value from the translated coefficient row. -/
private theorem cutoff_eq :
    middleK141Profile.eval (7 / 2) = (translated.num 0 : ℚ) / translated.den := by
  have hp := BData.poly_shift 31 7 2 (by decide +kernel) (by decide)
  rw [translated_ok] at hp
  have he := congrArg (fun P : Polynomial ℚ ↦ P.eval 0) hp
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    zero_add, Int.cast_ofNat] at he
  rw [← Polynomial.coeff_zero_eq_eval_zero, translated.poly_coeff (Nat.zero_le 31)] at he
  exact he.symm

/-- The K141 profile has bounded degree and a nonnegative value at the cutoff. -/
public theorem middle_k141_comp_profile :
    middleK141Profile.natDegree ≤ 31 ∧ 0 ≤ middleK141Profile.eval₂ (Rat.castHom ℝ) (7 / 2) := by
  constructor
  · exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos 31) _)
  · have hv : 0 ≤ middleK141Profile.eval (7 / 2) := by
      rw [cutoff_eq]
      decide +kernel
    have hm := Polynomial.eval_map_apply (p := middleK141Profile) (Rat.castHom ℝ) (7 / 2 : ℚ)
    rw [Polynomial.eval_map] at hm
    simp only [Rat.coe_castHom, Rat.cast_div, Rat.cast_ofNat] at hm
    exact hm.symm ▸ Rat.cast_nonneg.mpr hv

/-- The normalized K141 cutoff weight fits the common boundary budget. -/
public theorem middle_k141_cutoff_weight_le :
    (middleK141Norm : ℝ) * Real.exp (-(7 : ℝ)) * middleK141Profile.eval₂ (Rat.castHom ℝ) (7 / 2) ≤
      903 / 10000 := by
  have h := mul_le_mul_of_nonneg_right middle_k141_scale_le middle_k141_comp_profile.2
  refine h.trans ?_
  have hm := Polynomial.eval_map_apply (p := middleK141Profile) (Rat.castHom ℝ) (7 / 2 : ℚ)
  rw [Polynomial.eval_map] at hm
  simp only [Rat.coe_castHom, Rat.cast_div, Rat.cast_ofNat] at hm
  rw [hm]
  have hc : middleK141Scale * middleK141Profile.eval (7 / 2) ≤ (903 / 10000 : ℚ) := by
    rw [cutoff_eq]
    decide +kernel
  simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hc

/-- The integer cell widths for K141 compensation use a denominator of 128. -/
private def compWidths : List ℕ :=
  [21, 7, 7, 7, 7, 7, 7, 7, 56, 7, 7, 7, 7, 7, 7, 7, 273]

/-- The rational widths used by the analytic compensation formula. -/
private def compGrid : List ℚ :=
  compWidths.map (fun w : ℕ ↦ ((w : ℤ) : ℚ) / (128 : ℤ))

/-- Accumulate the outward-rounded charge pair before comparing with the two budgets. -/
private def compTotal : ℚ × ℚ :=
  middleCompTotal (BData.compGridCharge 31 128 (2) (3 / 2) (10 ^ 18)) compGrid 0

/-- Verify both rounded K141 charges against the analytic budgets. -/
private theorem comp_total_le :
    compTotal.1 ≤ (864821009060099 / 10 ^ 18 : ℚ) ∧
      compTotal.2 ≤ (14677708930678733 / 10 ^ 18 : ℚ) := by
  decide +kernel

/-- K141 admits a positive compensation partition with the two stated analytic budgets. -/
public theorem middle_k141_comp_budgets :
    ∃ hs : List ℚ,
      (∀ w ∈ hs, 0 < w) ∧
        hs.sum = 7 / 2 ∧
        (∫ v in (0 : ℝ)..(7 / 2 : ℝ),
            Real.exp (-(((2 : ℚ) : ℝ) + 1 / 2) * v) * middleCompOn middleK141Profile 31 hs 0 v) ≤
          864821009060099 / 10 ^ 18 ∧
        middleCompVariation middleK141Profile 31 (2) (3 / 2) hs 0 ≤
          14677708930678733 / 10 ^ 18 := by
  have hw : ∀ w ∈ compWidths, 0 < w := by decide +kernel
  have hsum : compGrid.sum = 7 / 2 := by decide +kernel
  have h :=
    BData.comp_grid_total_le 31 (b := 128) (a := 2) (d := 3 / 2) (S := 10 ^ 18) (I :=
      864821009060099 / 10 ^ 18) (V := 14677708930678733 / 10 ^ 18) (by decide +kernel) (by decide)
      (by norm_num only) (by norm_num only) compWidths hw comp_total_le.1 comp_total_le.2
  change
    (∫ v in (0 : ℝ)..(compGrid.sum : ℝ),
          Real.exp (-(((2) + 1 / 2 : ℚ) : ℝ) * v) *
            middleCompOn middleK141Profile 31 compGrid 0 v) ≤
        _ ∧
      middleCompVariation middleK141Profile 31 (2) (3 / 2) compGrid 0 ≤ _ at h
  refine ⟨compGrid, by decide +kernel, hsum, ?_⟩
  simpa only [hsum, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_add, Rat.cast_inv,
    Rat.cast_one] using h

/-- K141 has nonnegative derivatives beyond the checked reflection anchor. -/
public theorem middle_k141_tail_sign (j : ℕ) {t : ℝ} (ht : 20 ≤ t) :
    0 ≤ ((Polynomial.derivative^[j]) (middleK141Profile.map (Rat.castHom ℝ))).eval t := by
  exact
    BData.tail_signs 31 20 (by decide +kernel) (by decide +kernel) j
      (by simpa only [Int.cast_ofNat] using ht)

/-- The numerator row before squaring for the K141 contour kernel. -/
private def poleData : MiddleIntRow :=
  ⟨1000000000000,
    #[18625615630030854532, -74284131883121136289, 142893261953595074351, -173755161291173625846,
      147956062582679560233, -92581417258766358734, 43549705020716922112, -15503594983492148728,
      4155231568608976199, -824216882844235664, 117558045908069878, -11204865232843492,
      718433509112896, -33567803626046, 1000000000000]⟩

/-- The rational polynomial in the numerator of the K141 contour kernel. -/
public noncomputable def middleK141Kernel : Polynomial ℚ :=
  poleData.poly 14

/-- The K141 contour numerator has degree at most `14`. -/
public theorem middle_k141_kernel_degree : middleK141Kernel.natDegree ≤ 14 := by
  exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos 14) _)

/-- The K141 Euler profile is the inverse transform of its squared contour kernel. -/
public theorem middle_k141_profile_eq_pole :
    middleK141Profile = middlePoleProfile 31 middleK141Kernel := by
  have h :=
    BData.poly_eq_pole_profile poleData 31 (by decide +kernel) (by decide) (by decide +kernel)
  rw [poleData.poly_eq_of_size_le (M := 14) (by decide) (by decide)] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
