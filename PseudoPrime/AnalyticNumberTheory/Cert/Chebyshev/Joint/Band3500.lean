/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.BandSound
public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Band3100

/-! # Joint prefix verification from 3100 through 3499 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

private theorem band {n : ℕ} (hl : 3100 ≤ n) (hr : n < 3500) : thetaBand n = (19, 10) := by
  simp only [thetaBand, ite_eq_right (Nat.not_lt_of_ge hl), ite_eq_left hr]

private def extra3100 : ℕ → ℕ
  | 3100 => 34
  | 3135 => 23
  | _ => 0

private theorem part3100 :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (19 / 10 : ℝ) * Real.sqrt x)
      ⟨3100, 3097355316838818, 3097393709094831, 68735438166433, 68735438166554⟩
      ⟨3159, 3131149006734202, 3131187715819931, 70344876078865, 70344876078989⟩ := by
  apply
    accepted_band (a := 3100) (b := 3159) (by decide) (by decide) 19 10
      (fun _ hn hm ↦
        band (Nat.le_trans (by decide : 3100 ≤ 3100) hn)
          (Nat.lt_of_lt_of_le hm (by decide : 3159 ≤ 3500)))
      extra3100 2
  decide +kernel

private def extra3159 : ℕ → ℕ
  | 3159 => 7
  | 3167 => 16
  | 3184 => 15
  | 3200 => 15
  | _ => 0

private theorem part3159 :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (19 / 10 : ℝ) * Real.sqrt x)
      ⟨3159, 3131149006734202, 3131187715819931, 70344876078865, 70344876078989⟩
      ⟨3216, 3195675422897037, 3195714666653685, 70344876078865, 70344876078989⟩ := by
  apply
    accepted_band (a := 3159) (b := 3216) (by decide) (by decide) 19 10
      (fun _ hn hm ↦
        band (Nat.le_trans (by decide : 3100 ≤ 3159) hn)
          (Nat.lt_of_lt_of_le hm (by decide : 3216 ≤ 3500)))
      extra3159 4
  decide +kernel

private def extra3216 : ℕ → ℕ
  | 3216 => 16
  | 3233 => 24
  | _ => 0

private theorem part3216 :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (19 / 10 : ℝ) * Real.sqrt x)
      ⟨3216, 3195675422897037, 3195714666653685, 70344876078865, 70344876078989⟩
      ⟨3258, 3244171609917975, 3244211353186419, 70344876078865, 70344876078989⟩ := by
  apply
    accepted_band (a := 3216) (b := 3258) (by decide) (by decide) 19 10
      (fun _ hn hm ↦
        band (Nat.le_trans (by decide : 3100 ≤ 3216) hn)
          (Nat.lt_of_lt_of_le hm (by decide : 3258 ≤ 3500)))
      extra3216 2
  decide +kernel

private def extra3258 : ℕ → ℕ
  | 3258 => 23
  | 3282 => 16
  | 3299 => 7
  | _ => 0

private theorem part3258 :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (19 / 10 : ℝ) * Real.sqrt x)
      ⟨3258, 3244171609917975, 3244211353186419, 70344876078865, 70344876078989⟩
      ⟨3307, 3276556989074178, 3276597026354837, 70344876078865, 70344876078989⟩ := by
  apply
    accepted_band (a := 3258) (b := 3307) (by decide) (by decide) 19 10
      (fun _ hn hm ↦
        band (Nat.le_trans (by decide : 3100 ≤ 3258) hn)
          (Nat.lt_of_lt_of_le hm (by decide : 3307 ≤ 3500)))
      extra3258 3
  decide +kernel

private def extra3307 : ℕ → ℕ
  | 3307 => 15
  | 3323 => 24
  | _ => 0

private theorem part3307 :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (19 / 10 : ℝ) * Real.sqrt x)
      ⟨3307, 3276556989074178, 3276597026354837, 70344876078865, 70344876078989⟩
      ⟨3348, 3341434330453146, 3341474899441278, 70344876078865, 70344876078989⟩ := by
  apply
    accepted_band (a := 3307) (b := 3348) (by decide) (by decide) 19 10
      (fun _ hn hm ↦
        band (Nat.le_trans (by decide : 3100 ≤ 3307) hn)
          (Nat.lt_of_lt_of_le hm (by decide : 3348 ≤ 3500)))
      extra3307 2
  decide +kernel

private def extra3348 : ℕ → ℕ
  | 3348 => 32
  | _ => 0

private theorem part3348 :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (19 / 10 : ℝ) * Real.sqrt x)
      ⟨3348, 3341434330453146, 3341474899441278, 70344876078865, 70344876078989⟩
      ⟨3381, 3373920243302680, 3373961079725971, 70344876078865, 70344876078989⟩ := by
  apply
    accepted_band (a := 3348) (b := 3381) (by decide) (by decide) 19 10
      (fun _ hn hm ↦
        band (Nat.le_trans (by decide : 3100 ≤ 3348) hn)
          (Nat.lt_of_lt_of_le hm (by decide : 3381 ≤ 3500)))
      extra3348 1
  decide +kernel

private def extra3381 : ℕ → ℕ
  | 3381 => 32
  | _ => 0

private theorem part3381 :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (19 / 10 : ℝ) * Real.sqrt x)
      ⟨3381, 3373920243302680, 3373961079725971, 70344876078865, 70344876078989⟩
      ⟨3414, 3406446343620981, 3406487556146615, 70344876078865, 70344876078989⟩ := by
  apply
    accepted_band (a := 3381) (b := 3414) (by decide) (by decide) 19 10
      (fun _ hn hm ↦
        band (Nat.le_trans (by decide : 3100 ≤ 3381) hn)
          (Nat.lt_of_lt_of_le hm (by decide : 3414 ≤ 3500)))
      extra3381 1
  decide +kernel

private def extra3414 : ℕ → ℕ
  | 3414 => 32
  | 3447 => 7
  | 3455 => 8
  | _ => 0

private theorem part3414 :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (19 / 10 : ℝ) * Real.sqrt x)
      ⟨3414, 3406446343620981, 3406487556146615, 70344876078865, 70344876078989⟩
      ⟨3464, 3447180730706052, 3447222160613726, 70344876078865, 70344876078989⟩ := by
  apply
    accepted_band (a := 3414) (b := 3464) (by decide) (by decide) 19 10
      (fun _ hn hm ↦
        band (Nat.le_trans (by decide : 3100 ≤ 3414) hn)
          (Nat.lt_of_lt_of_le hm (by decide : 3464 ≤ 3500)))
      extra3414 3
  decide +kernel

private def extra3464 : ℕ → ℕ
  | 3464 => 24
  | 3489 => 10
  | _ => 0

private theorem part3464 :
    Segment Valid
      (fun x ↦
        |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
          |Chebyshev.theta x - x| ≤ (19 / 10 : ℝ) * Real.sqrt x)
      ⟨3464, 3447180730706052, 3447222160613726, 70344876078865, 70344876078989⟩
      ⟨3500, 3483879109733892, 3483920680466223, 74422413522765, 74422413522895⟩ := by
  apply
    accepted_band (a := 3464) (b := 3500) (by decide) (by decide) 19 10
      (fun _ hn hm ↦
        band (Nat.le_trans (by decide : 3100 ≤ 3464) hn)
          (Nat.lt_of_lt_of_le hm (by decide : 3500 ≤ 3500)))
      extra3464 2
  decide +kernel

/-- The incoming prefix extends to 3500 with the stated psi estimate. -/
theorem prefix3500 :
    Valid ⟨3500, 3483879109733892, 3483920680466223, 74422413522765, 74422413522895⟩ ∧
      ∀ x : ℝ,
        3100 ≤ x →
          x < 3500 →
          |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x ∧
            |Chebyshev.theta x - x| ≤ (19 / 10 : ℝ) * Real.sqrt x := by
  have joined0 := segment_comp part3100 part3159
  have joined1 := segment_comp part3216 part3258
  have joined2 := segment_comp part3307 part3348
  have joined3 := segment_comp part3381 part3414
  have joined4 := segment_comp joined0 joined1
  have joined5 := segment_comp joined2 joined3
  have joined6 := segment_comp joined4 joined5
  have joined7 := segment_comp joined6 part3464
  exact joined7 prefix3100.1

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
