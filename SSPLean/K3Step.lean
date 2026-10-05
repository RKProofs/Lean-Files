import SSPLean.K3FourthRenewal
import SSPLean.K3AllStagesComplete

/-!
# The `k = 3` state-return induction step in concrete moment coordinates

This discharges `SSP.K2Concrete.K3Inputs.step`.  The analytic core is
`SSP.K3AllStages.excursionReducedGap_nonneg_of_corner_faces`, which takes *general*
excursion second and third moments; the `mixtureWeight` change of variables of
`SSPLean.K3AllStagesCore` converts them into the mixture coordinates in which the corner
and face certificates are proved, and the degree-six scale lemmas absorb the resulting
time-scale factor.  The moment-side input is `SSPLean.K3FourthRenewal`.

The four hypotheses that the analytic core needs about each excursion are supplied by
results that are *already unconditional* in this repository:

* `hA`, `hB` (Aldous--Shepp at the parent order) — `transientInitialAldousSheppForParent`;
* `hC`, `hD` (the `k = 2` bound at the parent order) — `all_transient_initial_laws_direct`.

So no extra hypothesis beyond the `k = 3` inductive one is required.
-/

open Finset

namespace SSP.K2Concrete

open SSP.K3S4Renewal SSP.K3AllStages

/-- The `k = 2` bound at the parent order `n`, in the form `(n+1)A² ≤ n·u·C` that the
`k = 3` analytic core consumes.  This is `StageBound (n-1)` rewritten. -/
theorem k2_bound_for_parent {r n : ℕ} (hr : 1 ≤ r) (hrn : r < n)
    (X : TransientInitial r) :
    ((n : ℝ) + 1) * (transientInitialMoment2 r X) ^ 2 ≤
      (n : ℝ) * transientInitialMoment1 r X * transientInitialMoment3 r X := by
  have h0 := all_transient_initial_laws_direct hr X
  have hmono := SSP.K2AllStages.stageBound_mono hr (Nat.le_sub_one_of_lt hrn)
    (transientInitialMoment1_nonneg X) (transientInitialMoment2_nonneg X)
    (transientInitialMoment3_nonneg X) h0
  unfold SSP.K2AllStages.StageBound at hmono
  have hncast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hncast] at hmono
  norm_num at hmono
  nlinarith [hmono]

/-- The sharp corner in general coordinates.  Mirrors the change of variables used by
`SSP.K3AllStages.sharpSides_interior_impossible`: `p = mixtureWeight n u A`,
`q = mixtureWeight n v B`, time scale `L = r·u + (r+1)·x`, and then the degree-six scale
lemma transports the mixture-coordinate certificate back. -/
theorem sharpGap_nonneg_general
    (n r x u A v B : ℝ) (hn : 4 ≤ n) (hr : 0 < r) (hx : 0 ≤ x)
    (hu : 0 < u) (hv : 0 < v)
    (hA : n * u ^ 2 ≤ (n - 1) * A) (hB : n * v ^ 2 ≤ (n - 1) * B) :
    0 ≤ sharpGap n r x u A v B := by
  have hn0p : 0 < n := by linarith
  have hn0 : n ≠ 0 := hn0p.ne'
  have hnp1 : n + 1 ≠ 0 := by linarith
  have hAp : 0 < A := by nlinarith [sq_pos_of_pos hu]
  have hBp : 0 < B := by nlinarith [sq_pos_of_pos hv]
  let p := mixtureWeight n u A
  let q := mixtureWeight n v B
  let L := r * u + (r + 1) * x
  obtain ⟨hp, hp1⟩ := mixtureWeight_pos_le_one n u A (by linarith) hu hA
  obtain ⟨hq, hq1⟩ := mixtureWeight_pos_le_one n v B (by linarith) hv hB
  have hp' : 0 < p := by simpa [p] using hp
  have hq' : 0 < q := by simpa [q] using hq
  have hp1' : p ≤ 1 := by simpa [p] using hp1
  have hq1' : q ≤ 1 := by simpa [q] using hq1
  have hL : 0 < L := by
    dsimp [L]
    have : 0 < r * u := mul_pos hr hu
    positivity
  let a := r * u / L
  let Y := u / (p * L)
  let T := v / (q * L)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [div_le_one hL]
    dsimp [L]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r + 1) hx]
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  -- the six coordinate identities
  have hrid : a / (p * Y) = r := by
    dsimp [a, Y]
    field_simp [hp'.ne', hL.ne', hu.ne']
  have hxid : L * (p * Y * (1 - a) / (p * Y + a)) = x := by
    dsimp [a, Y, L]
    field_simp [hp'.ne', hL.ne', hu.ne']
    simp
    ring
  have huid : L * (p * Y) = u := by
    dsimp [Y]
    field_simp [hp'.ne', hL.ne']
  have hvid : L * (q * T) = v := by
    dsimp [T]
    field_simp [hq'.ne', hL.ne']
  have hAid : L ^ 2 * (n * p * Y ^ 2 / (n - 1)) = A := by
    dsimp [Y, p, mixtureWeight]
    field_simp [hn0, (by linarith : (n:ℝ) - 1 ≠ 0), hu.ne', hAp.ne', hL.ne']
  have hBid : L ^ 2 * (n * q * T ^ 2 / (n - 1)) = B := by
    dsimp [T, q, mixtureWeight]
    field_simp [hn0, (by linarith : (n:ℝ) - 1 ≠ 0), hv.ne', hBp.ne', hL.ne']
  -- transport the mixture-coordinate certificate
  have hcert := sharpGap_nonneg_of_uniform n a T Y p q hn ha hT hY hp' hq'
    (uniformSharpGap_nonneg n a T Y q hn ha.le ha1 hT hY hq' hq1')
  have hpY : p * Y ≠ 0 := by positivity
  have hqT : q * T ≠ 0 := by positivity
  have hAc : n * p * Y ^ 2 / (n - 1) ≠ 0 := by
    have : (0:ℝ) < n * p * Y ^ 2 / (n - 1) := by
      have h1 : (0:ℝ) < n - 1 := by linarith
      positivity
    exact this.ne'
  have hBc : n * q * T ^ 2 / (n - 1) ≠ 0 := by
    have : (0:ℝ) < n * q * T ^ 2 / (n - 1) := by
      have h1 : (0:ℝ) < n - 1 := by linarith
      positivity
    exact this.ne'
  have hscale := sharpGap_scale n L (a / (p * Y)) (p * Y * (1 - a) / (p * Y + a))
    (p * Y) (n * p * Y ^ 2 / (n - 1)) (q * T) (n * q * T ^ 2 / (n - 1))
    hn0 hnp1 hL.ne' hpY hqT hAc hBc
  rw [hrid] at hcert
  rw [hrid, hxid, huid, hAid, hvid, hBid] at hscale
  have hL6 : (0:ℝ) < L ^ 6 := by positivity
  rw [hscale]
  exact mul_nonneg hL6.le hcert

/-- The coordinate dictionary used by all three general-coordinate certificates: the
`mixtureWeight` change of variables together with the six identities that send the mixture
coordinates back to `(r, x, u, A, v, B)` at time scale `L`. -/
theorem mixture_coordinates_exist
    (n r x u A v B : ℝ) (hn : 4 ≤ n) (hr : 0 < r) (hx : 0 ≤ x)
    (hu : 0 < u) (hv : 0 < v)
    (hA : n * u ^ 2 ≤ (n - 1) * A) (hB : n * v ^ 2 ≤ (n - 1) * B) :
    ∃ a T Y p q L : ℝ,
      0 < a ∧ a ≤ 1 ∧ 0 < T ∧ 0 < Y ∧ 0 < p ∧ p ≤ 1 ∧ 0 < q ∧ q ≤ 1 ∧ 0 < L ∧
      a / (p * Y) = r ∧
      L * (p * Y * (1 - a) / (p * Y + a)) = x ∧
      L * (p * Y) = u ∧
      L ^ 2 * (n * p * Y ^ 2 / (n - 1)) = A ∧
      L * (q * T) = v ∧
      L ^ 2 * (n * q * T ^ 2 / (n - 1)) = B := by
  have hn0p : 0 < n := by linarith
  have hn0 : n ≠ 0 := hn0p.ne'
  have hAp : 0 < A := by nlinarith [sq_pos_of_pos hu]
  have hBp : 0 < B := by nlinarith [sq_pos_of_pos hv]
  let p := mixtureWeight n u A
  let q := mixtureWeight n v B
  let L := r * u + (r + 1) * x
  obtain ⟨hp, hp1⟩ := mixtureWeight_pos_le_one n u A (by linarith) hu hA
  obtain ⟨hq, hq1⟩ := mixtureWeight_pos_le_one n v B (by linarith) hv hB
  have hp' : 0 < p := by simpa [p] using hp
  have hq' : 0 < q := by simpa [q] using hq
  have hp1' : p ≤ 1 := by simpa [p] using hp1
  have hq1' : q ≤ 1 := by simpa [q] using hq1
  have hL : 0 < L := by
    dsimp [L]
    have : 0 < r * u := mul_pos hr hu
    positivity
  let a := r * u / L
  let Y := u / (p * L)
  let T := v / (q * L)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [div_le_one hL]
    dsimp [L]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r + 1) hx]
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨a, T, Y, p, q, L, ha, ha1, hT, hY, hp', hp1', hq', hq1', hL, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [a, Y]; field_simp [hp'.ne', hL.ne', hu.ne']
  · dsimp [a, Y, L]; field_simp [hp'.ne', hL.ne', hu.ne']; simp; ring
  · dsimp [Y]; field_simp [hp'.ne', hL.ne']
  · dsimp [Y, p, mixtureWeight]
    field_simp [hn0, (by linarith : (n:ℝ) - 1 ≠ 0), hu.ne', hAp.ne', hL.ne']
  · dsimp [T]; field_simp [hq'.ne', hL.ne']
  · dsimp [T, q, mixtureWeight]
    field_simp [hn0, (by linarith : (n:ℝ) - 1 ≠ 0), hv.ne', hBp.ne', hL.ne']

/-- Face A in general coordinates. -/
theorem sharpFaceA_nonneg_general
    (n r x u A v B : ℝ) (hn : 4 ≤ n) (hr : 0 < r) (hx : 0 ≤ x)
    (hu : 0 < u) (hv : 0 < v)
    (hA : n * u ^ 2 ≤ (n - 1) * A) (hB : n * v ^ 2 ≤ (n - 1) * B)
    (hgrad : sharpGradA n r x u A v B < 0)
    (hside : 0 ≤ sharpSideA n r x u A v B) :
    0 ≤ sharpFaceA n r x u A v B := by
  have hn0 : n ≠ 0 := by linarith
  have hnp1 : n + 1 ≠ 0 := by linarith
  obtain ⟨a, T, Y, p, q, L, ha, ha1, hT, hY, hp, hp1, hq, hq1, hL,
    hrid, hxid, huid, hAid, hvid, hBid⟩ :=
    mixture_coordinates_exist n r x u A v B hn hr hx hu hv hA hB
  have hpY : p * Y ≠ 0 := by positivity
  have hqT : q * T ≠ 0 := by positivity
  have hAc : n * p * Y ^ 2 / (n - 1) ≠ 0 := by
    have h1 : (0:ℝ) < n - 1 := by linarith
    have : (0:ℝ) < n * p * Y ^ 2 / (n - 1) := by positivity
    exact this.ne'
  have hBc : n * q * T ^ 2 / (n - 1) ≠ 0 := by
    have h1 : (0:ℝ) < n - 1 := by linarith
    have : (0:ℝ) < n * q * T ^ 2 / (n - 1) := by positivity
    exact this.ne'
  have hL6 : (0:ℝ) < L ^ 6 := by positivity
  -- transport the gradient and side hypotheses into mixture coordinates
  have hgA := sharpGradA_scale n L (a / (p * Y)) (p * Y * (1 - a) / (p * Y + a))
    (p * Y) (n * p * Y ^ 2 / (n - 1)) (q * T) (n * q * T ^ 2 / (n - 1))
    hn0 hnp1 hL.ne' hpY hqT hAc hBc
  have hsA := sharpSideA_scale n L (a / (p * Y)) (p * Y * (1 - a) / (p * Y + a))
    (p * Y) (n * p * Y ^ 2 / (n - 1)) (q * T) (n * q * T ^ 2 / (n - 1))
    hn0 hnp1 hL.ne' hpY hqT hAc hBc
  have hfA := sharpFaceA_scale n L (a / (p * Y)) (p * Y * (1 - a) / (p * Y + a))
    (p * Y) (n * p * Y ^ 2 / (n - 1)) (q * T) (n * q * T ^ 2 / (n - 1))
    hn0 hnp1 hL.ne' hpY hqT hAc hBc
  rw [hrid, hxid, huid, hAid, hvid, hBid] at hgA hsA hfA
  have hL3 : (0:ℝ) < L ^ 3 := by positivity
  have hgradM : sharpGradA n r (p * Y * (1 - a) / (p * Y + a))
      (p * Y) (n * p * Y ^ 2 / (n - 1)) (q * T) (n * q * T ^ 2 / (n - 1)) < 0 := by
    rw [hgA] at hgrad
    by_contra hc
    exact absurd hgrad (not_lt.mpr (mul_nonneg hL3.le (not_lt.mp hc)))
  have hsideM : 0 ≤ sharpSideA n r (p * Y * (1 - a) / (p * Y + a))
      (p * Y) (n * p * Y ^ 2 / (n - 1)) (q * T) (n * q * T ^ 2 / (n - 1)) := by
    rw [hsA] at hside
    exact nonneg_of_mul_nonneg_right hside hL3
  have hcert := sharpFaceA_nonneg_of_uniform n a T Y p q hn ha hT hY hp hq
    (uniformSharpFaceA_nonneg n a T Y q hn ha ha1 hT hY hq hq1)
    (by rw [hrid]; exact hgradM) (by rw [hrid]; exact hsideM)
  rw [hrid] at hcert
  rw [hfA]
  exact mul_nonneg hL6.le hcert

/-- Face B in general coordinates. -/
theorem sharpFaceB_nonneg_general
    (n r x u A v B : ℝ) (hn : 4 ≤ n) (hr : 0 < r) (hx : 0 ≤ x)
    (hu : 0 < u) (hv : 0 < v)
    (hA : n * u ^ 2 ≤ (n - 1) * A) (hB : n * v ^ 2 ≤ (n - 1) * B)
    (hgrad : sharpGradB n r x u A v B < 0)
    (hside : 0 ≤ sharpSideB n r x u A v B) :
    0 ≤ sharpFaceB n r x u A v B := by
  have hn0 : n ≠ 0 := by linarith
  have hnp1 : n + 1 ≠ 0 := by linarith
  obtain ⟨a, T, Y, p, q, L, ha, ha1, hT, hY, hp, hp1, hq, hq1, hL,
    hrid, hxid, huid, hAid, hvid, hBid⟩ :=
    mixture_coordinates_exist n r x u A v B hn hr hx hu hv hA hB
  have hpY : p * Y ≠ 0 := by positivity
  have hqT : q * T ≠ 0 := by positivity
  have hAc : n * p * Y ^ 2 / (n - 1) ≠ 0 := by
    have h1 : (0:ℝ) < n - 1 := by linarith
    have : (0:ℝ) < n * p * Y ^ 2 / (n - 1) := by positivity
    exact this.ne'
  have hBc : n * q * T ^ 2 / (n - 1) ≠ 0 := by
    have h1 : (0:ℝ) < n - 1 := by linarith
    have : (0:ℝ) < n * q * T ^ 2 / (n - 1) := by positivity
    exact this.ne'
  have hL6 : (0:ℝ) < L ^ 6 := by positivity
  have hgB := sharpGradB_scale n L (a / (p * Y)) (p * Y * (1 - a) / (p * Y + a))
    (p * Y) (n * p * Y ^ 2 / (n - 1)) (q * T) (n * q * T ^ 2 / (n - 1))
    hn0 hnp1 hL.ne' hpY hqT hAc hBc
  have hsB := sharpSideB_scale n L (a / (p * Y)) (p * Y * (1 - a) / (p * Y + a))
    (p * Y) (n * p * Y ^ 2 / (n - 1)) (q * T) (n * q * T ^ 2 / (n - 1))
    hn0 hnp1 hL.ne' hpY hqT hAc hBc
  have hfB := sharpFaceB_scale n L (a / (p * Y)) (p * Y * (1 - a) / (p * Y + a))
    (p * Y) (n * p * Y ^ 2 / (n - 1)) (q * T) (n * q * T ^ 2 / (n - 1))
    hn0 hnp1 hL.ne' hpY hqT hAc hBc
  rw [hrid, hxid, huid, hAid, hvid, hBid] at hgB hsB hfB
  have hL3 : (0:ℝ) < L ^ 3 := by positivity
  have hgradM : sharpGradB n r (p * Y * (1 - a) / (p * Y + a))
      (p * Y) (n * p * Y ^ 2 / (n - 1)) (q * T) (n * q * T ^ 2 / (n - 1)) < 0 := by
    rw [hgB] at hgrad
    by_contra hc
    exact absurd hgrad (not_lt.mpr (mul_nonneg hL3.le (not_lt.mp hc)))
  have hsideM : 0 ≤ sharpSideB n r (p * Y * (1 - a) / (p * Y + a))
      (p * Y) (n * p * Y ^ 2 / (n - 1)) (q * T) (n * q * T ^ 2 / (n - 1)) := by
    rw [hsB] at hside
    exact nonneg_of_mul_nonneg_right hside hL3
  have hcert := sharpFaceB_nonneg_of_uniform n a T Y p q hn ha hT hY hp hq
    (uniformSharpFaceB_nonneg n a T Y q hn ha ha1 hT hY hq hq1)
    (by rw [hrid]; exact hgradM) (by rw [hrid]; exact hsideM)
  rw [hrid] at hcert
  rw [hfB]
  exact mul_nonneg hL6.le hcert

/-- **The `k = 3` renewal gap in general coordinates.**  The analytic core with all three
certificates discharged.  This is the induction step in scalar form. -/
theorem excursionReducedGap_nonneg_general
    (n r x u A C v B D : ℝ)
    (hn : 4 ≤ n) (hr : 0 < r) (hx : 0 ≤ x) (hu : 0 < u) (hv : 0 < v)
    (hA : n * u ^ 2 ≤ (n - 1) * A) (hB : n * v ^ 2 ≤ (n - 1) * B)
    (hC : (n + 1) * A ^ 2 ≤ n * u * C) (hD : (n + 1) * B ^ 2 ≤ n * v * D) :
    0 ≤ excursionReducedGap n r x u A C v B D := by
  apply excursionReducedGap_nonneg_of_corner_faces n r x u A C v B D hn hr hx hu hv
    hA hB hC hD
  · exact sharpGap_nonneg_general n r x u A v B hn hr hx hu hv hA hB
  · intro hgrad hside
    exact sharpFaceA_nonneg_general n r x u A v B hn hr hx hu hv hA hB hgrad hside
  · intro hgrad hside
    exact sharpFaceB_nonneg_general n r x u A v B hn hr hx hu hv hA hB hgrad hside

/-- **The `k = 3` moment-level renewal step.**  Given, for both excursions, Aldous--Shepp
and the `k = 2` bound (both unconditional at the parent order) together with the `k = 3`
bound, the parent satisfies the `k = 3` bound at order `n`.

The `k = 3` hypotheses enter by lowering each excursion's fourth moment to its sharp
inductive value `(n+2)C²/((n+1)A)`, which is what `excursionReducedGap` evaluates;
`stageGap_fourth_mono` makes that a lower bound on the true gap. -/
theorem k3_renewal_step
    (n r x u A C E v B D F : ℝ)
    (hn : 4 ≤ n) (hr : 0 < r) (hx : 0 ≤ x) (hu : 0 < u) (hv : 0 < v)
    (hA : n * u ^ 2 ≤ (n - 1) * A) (hB : n * v ^ 2 ≤ (n - 1) * B)
    (hC : (n + 1) * A ^ 2 ≤ n * u * C) (hD : (n + 1) * B ^ 2 ≤ n * v * D)
    (hE : (n + 2) * C ^ 2 ≤ (n + 1) * A * E)
    (hF : (n + 2) * D ^ 2 ≤ (n + 1) * B * F) :
    0 ≤ stageGap n r
        (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C) (kernelM4 x u A C E)
        (kernelM1 x v) (kernelM2 x v B) (kernelM3 x v B D) (kernelM4 x v B D F) := by
  have hAp : 0 < A := by nlinarith [sq_pos_of_pos hu]
  have hBp : 0 < B := by nlinarith [sq_pos_of_pos hv]
  have hn1 : (0:ℝ) < n + 1 := by linarith
  -- the sharp lowered fourth moments
  have hEle : (n + 2) * C ^ 2 / ((n + 1) * A) ≤ E := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hE]
  have hFle : (n + 2) * D ^ 2 / ((n + 1) * B) ≤ F := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hF]
  have hk1u : (0:ℝ) ≤ kernelM1 x u := by unfold kernelM1; linarith
  have hk1v : (0:ℝ) ≤ kernelM1 x v := by unfold kernelM1; linarith
  have hk2u : (0:ℝ) ≤ kernelM2 x u A := by
    unfold kernelM2; nlinarith [sq_nonneg x, mul_nonneg hx hu.le]
  have hk2v : (0:ℝ) ≤ kernelM2 x v B := by
    unfold kernelM2; nlinarith [sq_nonneg x, mul_nonneg hx hv.le]
  have hmono := stageGap_fourth_mono n r
    (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C)
    (kernelM4 x u A C E) (kernelM4 x u A C ((n+2)*C^2/((n+1)*A)))
    (kernelM1 x v) (kernelM2 x v B) (kernelM3 x v B D)
    (kernelM4 x v B D F) (kernelM4 x v B D ((n+2)*D^2/((n+1)*B)))
    (by linarith) hr.le hk1u hk2u hk1v hk2v
    (by unfold kernelM4; linarith) (by unfold kernelM4; linarith)
  have hgap := excursionReducedGap_nonneg_general n r x u A C v B D
    hn hr hx hu hv hA hB hC hD
  unfold excursionReducedGap at hgap
  linarith [hmono, hgap]

end SSP.K2Concrete
