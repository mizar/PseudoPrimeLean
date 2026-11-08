/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028UniformLow

/-! # Rational local correction cells for the coefficient 0.28 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational endpoints, radii and correction lower bounds for the local
witness cells between logarithmic scales 16 and 30. The list supplies the
finite certificate used by the local witness theorem. -/
def target028LocalCells : List (ℚ × ℚ × ℚ × ℚ) :=
  [(16, 17711 / 1000, 1693280839 / 200000000, 3341299 / 1000000),
    (17711 / 1000, 19309 / 1000, 4685890147 / 500000000, 3501503 / 1000000),
    (19309 / 1000, 20777 / 1000, 10217362413 / 1000000000, 3634099 / 1000000),
    (20777 / 1000, 22107 / 1000, 10994154997 / 1000000000, 3744277 / 1000000),
    (22107 / 1000, 23301 / 1000, 5848962423 / 500000000, 3836101 / 1000000),
    (23301 / 1000, 6091 / 250, 12329730259 / 1000000000, 122281 / 31250),
    (6091 / 250, 3163 / 125, 3223054247 / 250000000, 994393 / 250000),
    (3163 / 125, 6533 / 250, 2677923647 / 200000000, 4031957 / 1000000),
    (6533 / 250, 13429 / 500, 3456938663 / 250000000, 1019483 / 250000),
    (13429 / 500, 27493 / 1000, 7105958871 / 500000000, 4116869 / 1000000),
    (27493 / 1000, 14023 / 500, 14547928159 / 1000000000, 4149941 / 1000000),
    (14023 / 500, 28527 / 1000, 7420274127 / 500000000, 2089017 / 500000),
    (28527 / 1000, 5789 / 200, 1509506953 / 100000000, 105049 / 25000),
    (5789 / 200, 29307 / 1000, 15316254339 / 1000000000, 2111191 / 500000),
    (29307 / 1000, 29621 / 1000, 7753903367 / 500000000, 4239799 / 1000000),
    (29621 / 1000, 29893 / 1000, 15673959917 / 1000000000, 4254711 / 1000000),
    (29893 / 1000, 30, 3954472197 / 250000000, 853497 / 200000)]

set_option maxRecDepth 8192 in
/-- Every listed radius has a certified strict correction margin, and the
endpoints satisfy the numerical cutoff inequalities. The exact rational
checks provide the arithmetic input for the local witness transfer. -/
theorem target028LocalCells_checked :
    target028LocalCells.all
        (fun (u, v, y, d) ↦
          localCorrectionCheck y (d + 1 / 100000000) (if y ≤ 11 then 3 else 4) &&
            decide (0 ≤ u ∧ u ≤ v ∧ y ^ 2 ≤ (7 / 25) * u ^ 2 ∧ (2 / 3) * v - d ≤ y)) =
      true := by
  decide +kernel

/-- Each listed interval supplies a radius and a strictly valid correction.
The certificate bounds both the radius and the shifted logarithm by the
0.28 cutoff throughout the interval. -/
theorem target028_local_cell_witness {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n) (hqn : q ∣ n)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ t : (ZMod q)ˣ, t ∈ H ∧ (t : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {u v y d : ℚ}
    (hm : (u, v, y, d) ∈ target028LocalCells) (hL : (u : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ (v : ℝ)) (hq : Real.log q ≤ (2 / 3 : ℝ) * Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hc := (List.all_eq_true.mp target028LocalCells_checked) (u, v, y, d) hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  have hcheck := hc.1
  have hdata := hc.2
  have hyq : (8 : ℚ) ≤ y := (of_decide_eq_true hcheck).1
  have hy : (8 : ℝ) ≤ y := by exact_mod_cast hyq
  have hcorr := localCorrectionCheck_sound hcheck
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hcorr
  have hstrict : (d : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection y := by
    linarith only [hcorr]
  obtain ⟨p, hp, hpbound, hf⟩ :=
    exists_prime_reject_of_local_shift hn ho hqn H hH hpass hGRH hy hstrict hq
  have hu : (0 : ℝ) ≤ u := by exact_mod_cast hdata.1
  have hy2 : (y : ℝ) ^ 2 ≤ (7 / 25 : ℝ) * (u : ℝ) ^ 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hdata.2.2.1
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using h
  have hv : (2 / 3 : ℝ) * v - d ≤ y := by
    have h := (Rat.cast_le (K := ℝ)).mpr hdata.2.2.2
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat] using h
  have hmxy : max (y : ℝ) ((2 / 3 : ℝ) * Real.log n - d) ≤ y := by
    apply max_le le_rfl
    linarith only [hU, hv]
  have hnonneg : (0 : ℝ) ≤ max (y : ℝ) ((2 / 3 : ℝ) * Real.log n - d) :=
    le_trans (by linarith only [hy]) (le_max_left _ _)
  have hsquare := mul_self_le_mul_self hnonneg hmxy
  have hs : (u : ℝ) ^ 2 ≤ (Real.log n) ^ 2 := by nlinarith only [hu, hL]
  have hfinal :
    (max (y : ℝ) ((2 / 3 : ℝ) * Real.log n - d)) ^ 2 ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by
    nlinarith only [hsquare, hy2, hs]
  exact ⟨p, hp, hpbound.trans hfinal, hf⟩

/-- Every logarithmic scale between 16 and 30 belongs to one certified local
cell. The rational endpoints form a closed, overlapping cover. -/
theorem target028_local_cell_cover (L : ℝ) (hL : 16 ≤ L) (hU : L ≤ 30) :
    ∃ u v y d : ℚ, (u, v, y, d) ∈ target028LocalCells ∧ (u : ℝ) ≤ L ∧ L ≤ (v : ℝ) := by
  by_cases h0 : L ≤ (17711 / 1000 : ℝ)
  · refine ⟨16, 17711 / 1000, 1693280839 / 200000000, 3341299 / 1000000, by decide +kernel, ?_, ?_⟩
    all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
    all_goals linarith only [hL, hU, h0]
  by_cases h1 : L ≤ (19309 / 1000 : ℝ)
  · refine
      ⟨17711 / 1000, 19309 / 1000, 4685890147 / 500000000, 3501503 / 1000000, by decide +kernel, ?_,
        ?_⟩
    all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
    all_goals linarith only [hL, hU, h0, h1]
  by_cases h2 : L ≤ (20777 / 1000 : ℝ)
  · refine
      ⟨19309 / 1000, 20777 / 1000, 10217362413 / 1000000000, 3634099 / 1000000, by decide +kernel,
        ?_, ?_⟩
    all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
    all_goals linarith only [hL, hU, h1, h2]
  by_cases h3 : L ≤ (22107 / 1000 : ℝ)
  · refine
      ⟨20777 / 1000, 22107 / 1000, 10994154997 / 1000000000, 3744277 / 1000000, by decide +kernel,
        ?_, ?_⟩
    all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
    all_goals linarith only [hL, hU, h2, h3]
  by_cases h4 : L ≤ (23301 / 1000 : ℝ)
  · refine
      ⟨22107 / 1000, 23301 / 1000, 5848962423 / 500000000, 3836101 / 1000000, by decide +kernel, ?_,
        ?_⟩
    all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
    all_goals linarith only [hL, hU, h3, h4]
  by_cases h5 : L ≤ (6091 / 250 : ℝ)
  · refine
      ⟨23301 / 1000, 6091 / 250, 12329730259 / 1000000000, 122281 / 31250, by decide +kernel, ?_,
        ?_⟩
    all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
    all_goals linarith only [hL, hU, h4, h5]
  by_cases h6 : L ≤ (3163 / 125 : ℝ)
  · refine
      ⟨6091 / 250, 3163 / 125, 3223054247 / 250000000, 994393 / 250000, by decide +kernel, ?_, ?_⟩
    all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
    all_goals linarith only [hL, hU, h5, h6]
  by_cases h7 : L ≤ (6533 / 250 : ℝ)
  · refine
      ⟨3163 / 125, 6533 / 250, 2677923647 / 200000000, 4031957 / 1000000, by decide +kernel, ?_, ?_⟩
    all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
    all_goals linarith only [hL, hU, h6, h7]
  by_cases h8 : L ≤ (13429 / 500 : ℝ)
  · refine
      ⟨6533 / 250, 13429 / 500, 3456938663 / 250000000, 1019483 / 250000, by decide +kernel, ?_, ?_⟩
    all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
    all_goals linarith only [hL, hU, h7, h8]
  by_cases h9 : L ≤ (27493 / 1000 : ℝ)
  · refine
      ⟨13429 / 500, 27493 / 1000, 7105958871 / 500000000, 4116869 / 1000000, by decide +kernel, ?_,
        ?_⟩
    all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
    all_goals linarith only [hL, hU, h8, h9]
  by_cases h10 : L ≤ (14023 / 500 : ℝ)
  · refine
      ⟨27493 / 1000, 14023 / 500, 14547928159 / 1000000000, 4149941 / 1000000, by decide +kernel,
        ?_, ?_⟩
    all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
    all_goals linarith only [hL, hU, h9, h10]
  by_cases h11 : L ≤ (28527 / 1000 : ℝ)
  · refine
      ⟨14023 / 500, 28527 / 1000, 7420274127 / 500000000, 2089017 / 500000, by decide +kernel, ?_,
        ?_⟩
    all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
    all_goals linarith only [hL, hU, h10, h11]
  by_cases h12 : L ≤ (5789 / 200 : ℝ)
  · refine
      ⟨28527 / 1000, 5789 / 200, 1509506953 / 100000000, 105049 / 25000, by decide +kernel, ?_, ?_⟩
    all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
    all_goals linarith only [hL, hU, h11, h12]
  by_cases h13 : L ≤ (29307 / 1000 : ℝ)
  · refine
      ⟨5789 / 200, 29307 / 1000, 15316254339 / 1000000000, 2111191 / 500000, by decide +kernel, ?_,
        ?_⟩
    all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
    all_goals linarith only [hL, hU, h12, h13]
  by_cases h14 : L ≤ (29621 / 1000 : ℝ)
  · refine
      ⟨29307 / 1000, 29621 / 1000, 7753903367 / 500000000, 4239799 / 1000000, by decide +kernel, ?_,
        ?_⟩
    all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
    all_goals linarith only [hL, hU, h13, h14]
  by_cases h15 : L ≤ (29893 / 1000 : ℝ)
  · refine
      ⟨29621 / 1000, 29893 / 1000, 15673959917 / 1000000000, 4254711 / 1000000, by decide +kernel,
        ?_, ?_⟩
    all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
    all_goals linarith only [hL, hU, h14, h15]
  refine ⟨29893 / 1000, 30, 3954472197 / 250000000, 853497 / 200000, by decide +kernel, ?_, ?_⟩
  all_goals norm_num only [Rat.cast_div, Rat.cast_ofNat]
  all_goals linarith only [hL, hU, h15]

/-- Under GRH, a proper local subgroup at a divisor of logarithmic size at
most two thirds of the input supplies a 0.28 witness on scales 16 through 30.
Choose the certified local cell containing the input scale. -/
theorem exists_prime_reject_028_local_16_30 {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n)
    (hqn : q ∣ n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ t : (ZMod q)ˣ, t ∈ H ∧ (t : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (16 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 30) (hq : Real.log q ≤ (2 / 3 : ℝ) * Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨u, v, y, d, hm, hlo, hhi⟩ := target028_local_cell_cover (Real.log n) hL hU
  exact target028_local_cell_witness hn ho hqn H hH hpass hGRH hm hlo hhi hq

/-- Under GRH, an odd integer with at least three prime factors counted with
multiplicity has a 0.28 witness on logarithmic scales 16 through 30. The two
smallest factors provide a divisor to which the local subgroup bound applies. -/
theorem exists_prime_reject_028_three_16_30 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hk : 3 ≤ ArithmeticFunction.cardFactors n) (hL : (16 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 30) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hk2 : 2 ≤ n.primeFactorsList.length := by
    change 2 ≤ ArithmeticFunction.cardFactors n
    exact le_trans (by norm_num only) hk
  obtain ⟨p, q, hp, hq, hd, hm⟩ :=
    NumberTheory.exists_prime_pair_log_mean (Nat.zero_lt_of_lt hn) hk2
  have hkR : (3 : ℝ) ≤ ArithmeticFunction.cardFactors n := Nat.cast_le.mpr hk
  have hkpos : (0 : ℝ) < ArithmeticFunction.cardFactors n := by linarith only [hkR]
  have hlog :
    Real.log ((p * q : ℕ) : ℝ) ≤ 2 * Real.log n / (ArithmeticFunction.cardFactors n : ℝ) := by
    apply (le_div_iff₀ hkpos).mpr
    simpa only [ArithmeticFunction.cardFactors_apply, mul_comm] using hm
  have hratio : 2 * Real.log n / (ArithmeticFunction.cardFactors n : ℝ) ≤ 2 * Real.log n / 3 :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num only) (Real.log_natCast_nonneg n))
      (by norm_num only) hkR
  rcases prime_pair_local_data hn ho hp hq hd with hthree | ⟨s, hs, hsn, hsp, H, hproper, hpass⟩
  · have hbound : (3 : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
    exact
      ⟨3, Nat.prime_three, hbound,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho Nat.prime_three hthree⟩
  · let : NeZero s := ⟨Nat.ne_zero_of_lt hs⟩
    have hslog : Real.log s ≤ (2 / 3 : ℝ) * Real.log n := by
      have h :=
        (Real.log_le_log (Nat.cast_pos.mpr hs) (Nat.cast_le.mpr hsp)).trans (hlog.trans hratio)
      linarith only [h]
    exact exists_prime_reject_028_local_16_30 hn ho hsn H hproper hpass hGRH hL hU hslog

/-- Under GRH, every uniform Korselt triple of logarithmic scale between 8 and
30 has a rejecting prime within the 0.28 cutoff. The finite classification,
rounded radius-eight bound and certified local cells cover the whole interval. -/
theorem uniformKorselt_reject_028_8_30 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 30) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h15 : Real.log n ≤ 15
  · exact uniformKorselt_reject_028_low hn ho hu hL h15
  have hk : 3 ≤ ArithmeticFunction.cardFactors n := by
    have h := List.toFinset_card_le n.primeFactorsList
    change n.primeFactors.card ≤ ArithmeticFunction.cardFactors n at h
    exact hu.2.1 ▸ h
  by_cases h16 : Real.log n ≤ 16
  · exact exists_prime_reject_028_three_15_16 hn ho hGRH hk (le_of_not_ge h15) h16
  · exact exists_prime_reject_028_three_16_30 hn ho hGRH hk (le_of_not_ge h16) hU

end PseudoPrime.PrimeTestBounds.MillerRabin
