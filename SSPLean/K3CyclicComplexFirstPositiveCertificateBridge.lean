import SSPLean.K3CyclicComplexFirstPositiveCertificateCore
import SSPLean.K3CyclicComplexFirstPositiveTime0To10
import SSPLean.K3CyclicComplexFirstPositiveTime11To20
import SSPLean.K3CyclicComplexFirstPositiveTime21To30
import SSPLean.K3CyclicComplexFirstPositiveTime31To40
import SSPLean.K3CyclicComplexFirstPositiveTime41To50
import SSPLean.K3CyclicComplexFirstPositiveTime51To60
import SSPLean.K3CyclicComplexFirstPositiveTime61To70

/-! # Full positive-m compact Taylor certificate -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.PositiveCoeff

open Dense

theorem certificateAtFrom_prefix_eq {a b k : ℕ}
    (hka : k < a) (hkb : k < b) :
    certificateAtFrom (powerTableUpTo a) k =
      certificateAtFrom (powerTableUpTo b) k := by
  unfold certificateAtFrom spatialBernTableFrom
  rw [timeBernPolyFrom_prefix_eq hka hkb]

theorem certificateAt_of_block {start count k : ℕ}
    (hblock : certificateBlock start count = true)
    (hk : k ∈ (List.range count).map (· + start)) :
    certificateAt k = true := by
  have hshared : certificateAtFrom (powerTableUpTo (start + count)) k = true := by
    simpa only [certificateBlock] using List.all_eq_true.mp hblock k hk
  unfold certificateAt
  rw [certificateAtFrom_prefix_eq (a := k + 1) (b := start + count)
    (by omega) (by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
      have := List.mem_range.mp hj
      omega)]
  exact hshared

theorem certificateAt_through_seventy {k : ℕ} (hk : k ≤ order) :
    certificateAt k = true := by
  have hk70 : k ≤ 70 := by simpa [order] using hk
  by_cases h10 : k ≤ 10
  · exact certificateAt_of_block certificate_time_zero_through_ten
      (List.mem_map.mpr ⟨k, List.mem_range.mpr (by omega), by omega⟩)
  by_cases h20 : k ≤ 20
  · exact certificateAt_of_block certificate_time_eleven_through_twenty
      (List.mem_map.mpr ⟨k - 11, List.mem_range.mpr (by omega), by omega⟩)
  by_cases h30 : k ≤ 30
  · exact certificateAt_of_block certificate_time_twenty_one_through_thirty
      (List.mem_map.mpr ⟨k - 21, List.mem_range.mpr (by omega), by omega⟩)
  by_cases h40 : k ≤ 40
  · exact certificateAt_of_block certificate_time_thirty_one_through_forty
      (List.mem_map.mpr ⟨k - 31, List.mem_range.mpr (by omega), by omega⟩)
  by_cases h50 : k ≤ 50
  · exact certificateAt_of_block certificate_time_forty_one_through_fifty
      (List.mem_map.mpr ⟨k - 41, List.mem_range.mpr (by omega), by omega⟩)
  by_cases h60 : k ≤ 60
  · exact certificateAt_of_block certificate_time_fifty_one_through_sixty
      (List.mem_map.mpr ⟨k - 51, List.mem_range.mpr (by omega), by omega⟩)
  · exact certificateAt_of_block certificate_time_sixty_one_through_seventy
      (List.mem_map.mpr ⟨k - 61, List.mem_range.mpr (by omega), by omega⟩)

theorem compactTaylor_ge_one
    {r t u : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    1 ≤ compactTaylorFrom (powerTableUpTo (order + 1)) r t u := by
  rw [compactTaylorFrom_eq_timeBernstein]
  have hsumU := sum_real_bernsteinBasis order u
  calc
    1 = ∑ k ∈ Finset.range (order + 1),
        (Nat.choose order k : ℝ) * u ^ k *
          (1 - u) ^ (order - k) := hsumU.symm
    _ ≤ ∑ k ∈ Finset.range (order + 1),
        beval (timeBernPolyFrom (powerTableUpTo (order + 1)) k) r t *
          ((Nat.choose order k : ℝ) * u ^ k *
            (1 - u) ^ (order - k)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkOrder : k ≤ order :=
        Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hqPrefix := beval_timeBernPoly_ge_one hkOrder
        (certificateAt_through_seventy hkOrder) hr0 hr1 ht0 ht1
      have heq := timeBernPolyFrom_prefix_eq
        (a := k + 1) (b := order + 1) (k := k) (by omega) (by omega)
      have hq : 1 ≤
          beval (timeBernPolyFrom (powerTableUpTo (order + 1)) k) r t := by
        rw [← heq]
        exact hqPrefix
      have hbasis : 0 ≤ (Nat.choose order k : ℝ) * u ^ k *
          (1 - u) ^ (order - k) := by positivity
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hq hbasis

end SSP.K3CyclicComplex.PositiveCoeff
