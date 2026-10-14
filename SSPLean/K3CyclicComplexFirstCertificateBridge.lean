import SSPLean.K3CyclicComplexFirstCertificateCore
import SSPLean.K3CyclicComplexFirstCoeff31To40
import SSPLean.K3CyclicComplexFirstCoeff41To50
import SSPLean.K3CyclicComplexFirstCoeff51To60
import SSPLean.K3CyclicComplexFirstCoeff61To70

/-! # Semantic bridge for the complex first-start compact certificate

This module turns the executable rational certificates into kernel-checked
nonnegativity statements for their real evaluations on the unit square.
-/

set_option autoImplicit false

namespace SSP.K3CyclicComplex

namespace ComplexCoeff

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

end ComplexCoeff

end SSP.K3CyclicComplex
