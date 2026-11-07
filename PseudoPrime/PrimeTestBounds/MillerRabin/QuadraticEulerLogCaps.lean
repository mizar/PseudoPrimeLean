/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerAggregate
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerLogSum

/-! # Certified logarithm sums for the Chebyshev boundary -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 20000

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows0LogLower : ℚ :=
  (692724599 / 500000)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows0_log_lower_check :
    centerRows0LogLower ≤ (centerRows0.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows0_mangoldt_lower :
    (centerRows0LogLower : ℝ) ≤
      (centerRows0.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows0 centerRows0LogLower centerRows0_check
    centerRows0_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows250LogLower : ℚ :=
  (1883006281 / 1000000)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows250_log_lower_check :
    centerRows250LogLower ≤ (centerRows250.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows250_mangoldt_lower :
    (centerRows250LogLower : ℝ) ≤
      (centerRows250.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows250 centerRows250LogLower centerRows250_check
    centerRows250_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows500LogLower : ℚ :=
  (1027183633 / 500000)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows500_log_lower_check :
    centerRows500LogLower ≤ (centerRows500.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows500_mangoldt_lower :
    (centerRows500LogLower : ℝ) ≤
      (centerRows500.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows500 centerRows500LogLower centerRows500_check
    centerRows500_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows750LogLower : ℚ :=
  (2167531999 / 1000000)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows750_log_lower_check :
    centerRows750LogLower ≤ (centerRows750.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows750_mangoldt_lower :
    (centerRows750LogLower : ℝ) ≤
      (centerRows750.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows750 centerRows750LogLower centerRows750_check
    centerRows750_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows1000LogLower : ℚ :=
  (2247194051 / 1000000)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows1000_log_lower_check :
    centerRows1000LogLower ≤ (centerRows1000.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows1000_mangoldt_lower :
    (centerRows1000LogLower : ℝ) ≤
      (centerRows1000.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows1000 centerRows1000LogLower centerRows1000_check
    centerRows1000_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows1250LogLower : ℚ :=
  (460945293 / 200000)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows1250_log_lower_check :
    centerRows1250LogLower ≤ (centerRows1250.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows1250_mangoldt_lower :
    (centerRows1250LogLower : ℝ) ≤
      (centerRows1250.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows1250 centerRows1250LogLower centerRows1250_check
    centerRows1250_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows1500LogLower : ℚ :=
  (590248381 / 250000)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows1500_log_lower_check :
    centerRows1500LogLower ≤ (centerRows1500.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows1500_mangoldt_lower :
    (centerRows1500LogLower : ℝ) ≤
      (centerRows1500.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows1500 centerRows1500LogLower centerRows1500_check
    centerRows1500_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows1750LogLower : ℚ :=
  (95367473 / 40000)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows1750_log_lower_check :
    centerRows1750LogLower ≤ (centerRows1750.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows1750_mangoldt_lower :
    (centerRows1750LogLower : ℝ) ≤
      (centerRows1750.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows1750 centerRows1750LogLower centerRows1750_check
    centerRows1750_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows2000LogLower : ℚ :=
  (1215867323 / 500000)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows2000_log_lower_check :
    centerRows2000LogLower ≤ (centerRows2000.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows2000_mangoldt_lower :
    (centerRows2000LogLower : ℝ) ≤
      (centerRows2000.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows2000 centerRows2000LogLower centerRows2000_check
    centerRows2000_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows2250LogLower : ℚ :=
  (1233937587 / 500000)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows2250_log_lower_check :
    centerRows2250LogLower ≤ (centerRows2250.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows2250_mangoldt_lower :
    (centerRows2250LogLower : ℝ) ≤
      (centerRows2250.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows2250 centerRows2250LogLower centerRows2250_check
    centerRows2250_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows2500LogLower : ℚ :=
  (1249860541 / 500000)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows2500_log_lower_check :
    centerRows2500LogLower ≤ (centerRows2500.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows2500_mangoldt_lower :
    (centerRows2500LogLower : ℝ) ≤
      (centerRows2500.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows2500 centerRows2500LogLower centerRows2500_check
    centerRows2500_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows2750LogLower : ℚ :=
  (2518968027 / 1000000)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows2750_log_lower_check :
    centerRows2750LogLower ≤ (centerRows2750.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows2750_mangoldt_lower :
    (centerRows2750LogLower : ℝ) ≤
      (centerRows2750.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows2750 centerRows2750LogLower centerRows2750_check
    centerRows2750_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows3000LogLower : ℚ :=
  (1273461577 / 500000)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows3000_log_lower_check :
    centerRows3000LogLower ≤ (centerRows3000.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows3000_mangoldt_lower :
    (centerRows3000LogLower : ℝ) ≤
      (centerRows3000.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows3000 centerRows3000LogLower centerRows3000_check
    centerRows3000_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows3250LogLower : ℚ :=
  (2569774609 / 1000000)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows3250_log_lower_check :
    centerRows3250LogLower ≤ (centerRows3250.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows3250_mangoldt_lower :
    (centerRows3250LogLower : ℝ) ≤
      (centerRows3250.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows3250 centerRows3250LogLower centerRows3250_check
    centerRows3250_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows3500LogLower : ℚ :=
  (2581785363 / 1000000)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows3500_log_lower_check :
    centerRows3500LogLower ≤ (centerRows3500.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows3500_mangoldt_lower :
    (centerRows3500LogLower : ℝ) ≤
      (centerRows3500.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows3500 centerRows3500LogLower centerRows3500_check
    centerRows3500_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows3750LogLower : ℚ :=
  (2615386823 / 1000000)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows3750_log_lower_check :
    centerRows3750LogLower ≤ (centerRows3750.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows3750_mangoldt_lower :
    (centerRows3750LogLower : ℝ) ≤
      (centerRows3750.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows3750 centerRows3750LogLower centerRows3750_check
    centerRows3750_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows4000LogLower : ℚ :=
  (40977227 / 15625)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows4000_log_lower_check :
    centerRows4000LogLower ≤ (centerRows4000.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows4000_mangoldt_lower :
    (centerRows4000LogLower : ℝ) ≤
      (centerRows4000.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows4000 centerRows4000LogLower centerRows4000_check
    centerRows4000_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows4250LogLower : ℚ :=
  (82974747 / 31250)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows4250_log_lower_check :
    centerRows4250LogLower ≤ (centerRows4250.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows4250_mangoldt_lower :
    (centerRows4250LogLower : ℝ) ≤
      (centerRows4250.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows4250 centerRows4250LogLower centerRows4250_check
    centerRows4250_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows4500LogLower : ℚ :=
  (106608111 / 40000)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows4500_log_lower_check :
    centerRows4500LogLower ≤ (centerRows4500.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows4500_mangoldt_lower :
    (centerRows4500LogLower : ℝ) ≤
      (centerRows4500.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows4500 centerRows4500LogLower centerRows4500_check
    centerRows4500_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows4750LogLower : ℚ :=
  (2685887237 / 1000000)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows4750_log_lower_check :
    centerRows4750LogLower ≤ (centerRows4750.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows4750_mangoldt_lower :
    (centerRows4750LogLower : ℝ) ≤
      (centerRows4750.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows4750 centerRows4750LogLower centerRows4750_check
    centerRows4750_log_lower_check

/-- Outward lower cap for the sum of prime-base logarithms in this block.
Kernel arithmetic checks this scalar against the certified row endpoints. -/
def centerRows5000LogLower : ℚ :=
  (2337508779 / 1000000)

/-- The proposed lower scalar is below the exact sum of logarithm endpoints.
The following real bound uses the existing root and logarithm certificates. -/
theorem centerRows5000_log_lower_check :
    centerRows5000LogLower ≤ (centerRows5000.map (fun r ↦ r.lo)).sum := by decide +kernel

/-- This block's actual Mangoldt sum is above its certified logarithm cap.
This supplies one contribution to the complete Chebyshev lower bound. -/
theorem centerRows5000_mangoldt_lower :
    (centerRows5000LogLower : ℝ) ≤
      (centerRows5000.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum :=
  checked_rows_mangoldt_lower centerRows5000 centerRows5000LogLower centerRows5000_check
    centerRows5000_log_lower_check

/-- Rational sum of all independently checked logarithm lower caps.
This sum is used only for the finite Chebyshev boundary certificate. -/
def centerRows50000LogLower : ℚ :=
  centerRows0LogLower + centerRows250LogLower + centerRows500LogLower + centerRows750LogLower +
    centerRows1000LogLower +
    centerRows1250LogLower +
    centerRows1500LogLower +
    centerRows1750LogLower +
    centerRows2000LogLower +
    centerRows2250LogLower +
    centerRows2500LogLower +
    centerRows2750LogLower +
    centerRows3000LogLower +
    centerRows3250LogLower +
    centerRows3500LogLower +
    centerRows3750LogLower +
    centerRows4000LogLower +
    centerRows4250LogLower +
    centerRows4500LogLower +
    centerRows4750LogLower +
    centerRows5000LogLower

/-- The certified logarithm lower caps total at least 49985.95. -/
theorem centerRows50000_log_lower_check : 999719 / 20 ≤ centerRows50000LogLower := by decide +kernel

/-- Add the actual Mangoldt lower bounds of all numerical blocks.
The support identity is applied separately to identify this with psi. -/
theorem center50000_rows_mangoldt_lower :
    (centerRows50000LogLower : ℝ) ≤
      (centerRows50000.map (fun r ↦ ArithmeticFunction.vonMangoldt (r.p ^ (r.k + 1)))).sum := by
  simp only [centerRows50000, List.map_append, List.sum_append, centerRows50000LogLower,
    Rat.cast_add, add_assoc]
  exact
    add_le_add centerRows0_mangoldt_lower
      (add_le_add centerRows250_mangoldt_lower
        (add_le_add centerRows500_mangoldt_lower
          (add_le_add centerRows750_mangoldt_lower
            (add_le_add centerRows1000_mangoldt_lower
              (add_le_add centerRows1250_mangoldt_lower
                (add_le_add centerRows1500_mangoldt_lower
                  (add_le_add centerRows1750_mangoldt_lower
                    (add_le_add centerRows2000_mangoldt_lower
                      (add_le_add centerRows2250_mangoldt_lower
                        (add_le_add centerRows2500_mangoldt_lower
                          (add_le_add centerRows2750_mangoldt_lower
                            (add_le_add centerRows3000_mangoldt_lower
                              (add_le_add centerRows3250_mangoldt_lower
                                (add_le_add centerRows3500_mangoldt_lower
                                  (add_le_add centerRows3750_mangoldt_lower
                                    (add_le_add centerRows4000_mangoldt_lower
                                      (add_le_add centerRows4250_mangoldt_lower
                                        (add_le_add centerRows4500_mangoldt_lower
                                          (add_le_add centerRows4750_mangoldt_lower
                                            (centerRows5000_mangoldt_lower))))))))))))))))))))

end PseudoPrime.PrimeTestBounds.MillerRabin
