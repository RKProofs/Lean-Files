import SSPLean.K3CyclicComplexFirstNegativeCertificateCore
import SSPLean.K3CyclicComplexFirstNegativeCoeff31To40
import SSPLean.K3CyclicComplexFirstNegativeCoeff41To50
import SSPLean.K3CyclicComplexFirstNegativeCoeff51To60
import SSPLean.K3CyclicComplexFirstNegativeCoeff61To70

/-! # Complete negative-m compact coefficient certificate through degree 70 -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.NegativeCoeff

theorem certificate_through_seventy {N : ℕ} (hN : N ≤ 70) :
    certificateOK N = true := by
  by_cases h10 : N ≤ 10
  · exact List.all_eq_true.mp certificate_through_ten N
      (List.mem_range.mpr (by omega))
  by_cases h20 : N ≤ 20
  · exact List.all_eq_true.mp certificate_eleven_through_twenty N
      (List.mem_map.mpr ⟨N - 11, List.mem_range.mpr (by omega), by omega⟩)
  by_cases h30 : N ≤ 30
  · exact List.all_eq_true.mp certificate_twenty_one_through_thirty N
      (List.mem_map.mpr ⟨N - 21, List.mem_range.mpr (by omega), by omega⟩)
  by_cases h40 : N ≤ 40
  · exact List.all_eq_true.mp certificate_thirty_one_through_forty N
      (List.mem_map.mpr ⟨N - 31, List.mem_range.mpr (by omega), by omega⟩)
  by_cases h50 : N ≤ 50
  · exact List.all_eq_true.mp certificate_forty_one_through_fifty N
      (List.mem_map.mpr ⟨N - 41, List.mem_range.mpr (by omega), by omega⟩)
  by_cases h60 : N ≤ 60
  · exact List.all_eq_true.mp certificate_fifty_one_through_sixty N
      (List.mem_map.mpr ⟨N - 51, List.mem_range.mpr (by omega), by omega⟩)
  · exact List.all_eq_true.mp certificate_sixty_one_through_seventy N
      (List.mem_map.mpr ⟨N - 61, List.mem_range.mpr (by omega), by omega⟩)

theorem curvatureCoefficient_nonneg_through_seventy {N : ℕ} (hN : N ≤ 70)
    {r t : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ Dense.beval (curvatureCoefficient N) r t :=
  curvatureCoefficient_nonneg_of_certificate
    (certificate_through_seventy hN) hr0 hr1 ht0 ht1

end SSP.K3CyclicComplex.NegativeCoeff
