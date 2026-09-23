import SSPLean.K3AllStagesUniform

set_option autoImplicit false

namespace SSP.K3AllStages

open SSP.K3S4Renewal
open SSP.K3S4KKT

/-- Consequently the strict interior KKT alternative is impossible throughout
the normalized mixture box at every stage `n ≥ 4`. -/
theorem sharpSides_interior_impossible_mixture_coordinates
    (n a T Y p q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hp : 0 < p) (hq : 0 < q) (hq1 : q ≤ 1)
    (hsideA : sharpSideA n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) < 0)
    (hsideB : sharpSideB n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) < 0) : False := by
  apply sharpSides_interior_impossible_of_uniform_implication
    n a T Y p q (by linarith) ha hT hY hp hq
  · intro hreturn
    exact uniformTerminalSide_nonneg_of_returnSide_pos
      n a T Y q hn ha ha1 hT hY hq hq1 hreturn
  · exact hsideA
  · exact hsideB

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem sharpGradA_scale
    (n L r x u A v B : ℝ) (hn0 : n ≠ 0) (hnp1 : n+1 ≠ 0)
    (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (hA : A ≠ 0) (_hB : B ≠ 0) :
    sharpGradA n r (L*x) (L*u) (L^2*A) (L*v) (L^2*B) =
      L^3*sharpGradA n r x u A v B := by
  unfold sharpGradA sharpThird excursionGradA excursionHAA excursionReducedGap
  unfold stageGap hessianCore geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4
  field_simp [hn0, hnp1, hL, hu, hv, hA, _hB]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem sharpGradB_scale
    (n L r x u A v B : ℝ) (hn0 : n ≠ 0) (hnp1 : n+1 ≠ 0)
    (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (_hA : A ≠ 0) (hB : B ≠ 0) :
    sharpGradB n r (L*x) (L*u) (L^2*A) (L*v) (L^2*B) =
      L^3*sharpGradB n r x u A v B := by
  unfold sharpGradB sharpThird excursionGradB excursionHBB excursionReducedGap
  unfold stageGap hessianCore geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4
  field_simp [hn0, hnp1, hL, hu, hv, _hA, hB]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The sharp-corner gap is homogeneous of degree six in the time scale. -/
theorem sharpGap_scale
    (n L r x u A v B : ℝ) (hn0 : n ≠ 0) (_hnp1 : n+1 ≠ 0)
    (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (_hA : A ≠ 0) (_hB : B ≠ 0) :
    sharpGap n r (L*x) (L*u) (L^2*A) (L*v) (L^2*B) =
      L^6*sharpGap n r x u A v B := by
  unfold sharpGap sharpThird excursionReducedGap stageGap
  unfold geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4
  field_simp [hn0, hL, hu, hv, _hA, _hB]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem sharpSideA_scale
    (n L r x u A v B : ℝ) (hn0 : n ≠ 0) (hnp1 : n+1 ≠ 0)
    (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) :
    sharpSideA n r (L*x) (L*u) (L^2*A) (L*v) (L^2*B) =
      L^3*sharpSideA n r x u A v B := by
  unfold sharpSideA
  rw [sharpGradA_scale n L r x u A v B hn0 hnp1 hL hu hv hA hB,
    sharpGradB_scale n L r x u A v B hn0 hnp1 hL hu hv hA hB]
  unfold excursionHAA excursionHAB hessianCore
  field_simp [hnp1, hL, hA, hB]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem sharpSideB_scale
    (n L r x u A v B : ℝ) (hn0 : n ≠ 0) (hnp1 : n+1 ≠ 0)
    (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) :
    sharpSideB n r (L*x) (L*u) (L^2*A) (L*v) (L^2*B) =
      L^3*sharpSideB n r x u A v B := by
  unfold sharpSideB
  rw [sharpGradA_scale n L r x u A v B hn0 hnp1 hL hu hv hA hB,
    sharpGradB_scale n L r x u A v B hn0 hnp1 hL hu hv hA hB]
  unfold excursionHBB excursionHAB hessianCore
  field_simp [hnp1, hL, hA, hB]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- Both one-face KKT discriminants are homogeneous of degree six. -/
theorem sharpFaceA_scale
    (n L r x u A v B : ℝ) (hn0 : n ≠ 0) (hnp1 : n+1 ≠ 0)
    (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) :
    sharpFaceA n r (L*x) (L*u) (L^2*A) (L*v) (L^2*B) =
      L^6*sharpFaceA n r x u A v B := by
  unfold sharpFaceA
  rw [sharpGap_scale n L r x u A v B hn0 hnp1 hL hu hv hA hB,
    sharpGradA_scale n L r x u A v B hn0 hnp1 hL hu hv hA hB]
  unfold excursionHAA hessianCore
  field_simp [hnp1, hL, hA, hB]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem sharpFaceB_scale
    (n L r x u A v B : ℝ) (hn0 : n ≠ 0) (hnp1 : n+1 ≠ 0)
    (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) :
    sharpFaceB n r (L*x) (L*u) (L^2*A) (L*v) (L^2*B) =
      L^6*sharpFaceB n r x u A v B := by
  unfold sharpFaceB
  rw [sharpGap_scale n L r x u A v B hn0 hnp1 hL hu hv hA hB,
    sharpGradB_scale n L r x u A v B hn0 hnp1 hL hu hv hA hB]
  unfold excursionHBB hessianCore
  field_simp [hnp1, hL, hA, hB]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The interior KKT candidate is impossible in the original renewal
coordinates for every stage `n ≥ 4`. -/
theorem sharpSides_interior_impossible
    (n r x u A v B : ℝ) (hn : 4 ≤ n) (hr : 0 < r) (hx : 0 ≤ x)
    (hu : 0 < u) (hv : 0 < v)
    (hA : n*u^2 ≤ (n-1)*A) (hB : n*v^2 ≤ (n-1)*B)
    (hsideA : sharpSideA n r x u A v B < 0)
    (hsideB : sharpSideB n r x u A v B < 0) : False := by
  have hn0p : 0 < n := by linarith
  have hn0 : n ≠ 0 := hn0p.ne'
  have hn1p : 0 < n-1 := by linarith
  have hnp1 : n+1 ≠ 0 := by linarith
  have hAp : 0 < A := by nlinarith [sq_pos_of_pos hu]
  have hBp : 0 < B := by nlinarith [sq_pos_of_pos hv]
  let p := mixtureWeight n u A
  let q := mixtureWeight n v B
  let L := r*u+(r+1)*x
  let a := r*u/L
  let Y := u/(p*L)
  let T := v/(q*L)
  obtain ⟨hp, hp1⟩ := mixtureWeight_pos_le_one n u A (by linarith) hu hA
  obtain ⟨hq, hq1⟩ := mixtureWeight_pos_le_one n v B (by linarith) hv hB
  have hp' : 0 < p := by simpa [p] using hp
  have hq' : 0 < q := by simpa [q] using hq
  have hp1' : p ≤ 1 := by simpa [p] using hp1
  have hq1' : q ≤ 1 := by simpa [q] using hq1
  have hL : 0 < L := by
    dsimp [L]
    have : 0 < r*u := mul_pos hr hu
    positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [div_le_one hL]
    dsimp [L]
    nlinarith [mul_nonneg (by linarith : 0 ≤ r+1) hx]
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hrid : a/(p*Y) = r := by
    dsimp [a, Y]
    field_simp [hp'.ne', hL.ne', hu.ne']
  have hxid : L*(p*Y*(1-a)/(p*Y+a)) = x := by
    dsimp [a, Y, L]
    field_simp [hp'.ne', hL.ne', hu.ne']
    simp
    ring
  have huid : L*(p*Y) = u := by
    dsimp [Y]
    field_simp [hp'.ne', hL.ne']
  have hvid : L*(q*T) = v := by
    dsimp [T]
    field_simp [hq'.ne', hL.ne']
  have hAid : L^2*(n*p*Y^2/(n-1)) = A := by
    dsimp [Y, p, mixtureWeight]
    field_simp [hn0, hn1p.ne', hu.ne', hAp.ne', hL.ne']
  have hBid : L^2*(n*q*T^2/(n-1)) = B := by
    dsimp [T, q, mixtureWeight]
    field_simp [hn0, hn1p.ne', hv.ne', hBp.ne', hL.ne']
  have hscaleA := sharpSideA_scale n L (a/(p*Y))
    (p*Y*(1-a)/(p*Y+a)) (p*Y) (n*p*Y^2/(n-1))
    (q*T) (n*q*T^2/(n-1)) hn0 hnp1 hL.ne'
    (by positivity) (by positivity) (by positivity) (by positivity)
  rw [hrid, hxid, huid, hAid, hvid, hBid] at hscaleA
  rw [hscaleA] at hsideA
  have hL3 : 0 < L^3 := by positivity
  have hsideANormR : sharpSideA n r (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) < 0 :=
    by
      by_contra hnot
      have hnonneg : 0 ≤ sharpSideA n r (p*Y*(1-a)/(p*Y+a))
          (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) := le_of_not_gt hnot
      have := mul_nonneg hL3.le hnonneg
      linarith
  have hsideANorm : sharpSideA n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) < 0 := by
    rw [hrid]
    exact hsideANormR
  have hscaleB := sharpSideB_scale n L (a/(p*Y))
    (p*Y*(1-a)/(p*Y+a)) (p*Y) (n*p*Y^2/(n-1))
    (q*T) (n*q*T^2/(n-1)) hn0 hnp1 hL.ne'
    (by positivity) (by positivity) (by positivity) (by positivity)
  rw [hrid, hxid, huid, hAid, hvid, hBid] at hscaleB
  rw [hscaleB] at hsideB
  have hsideBNormR : sharpSideB n r (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) < 0 :=
    by
      by_contra hnot
      have hnonneg : 0 ≤ sharpSideB n r (p*Y*(1-a)/(p*Y+a))
          (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) := le_of_not_gt hnot
      have := mul_nonneg hL3.le hnonneg
      linarith
  have hsideBNorm : sharpSideB n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) < 0 := by
    rw [hrid]
    exact hsideBNormR
  exact sharpSides_interior_impossible_mixture_coordinates
    n a T Y p q hn ha ha1 hT hY hp' hq' hq1' hsideANorm hsideBNorm

/-- Uniform reduction of arbitrary admissible third moments to the sharp corner,
two boundary faces, and the possible interior KKT point. -/
theorem excursionReducedGap_nonneg_of_sharp_certificates
    (n r x u A C v B D : ℝ)
    (hn : 2 ≤ n) (hr : 0 < r) (hx : 0 ≤ x)
    (hu : 0 < u) (hA : 0 < A) (hv : 0 < v) (hB : 0 < B)
    (hC : (n+1)*A^2 ≤ n*u*C) (hD : (n+1)*B^2 ≤ n*v*D)
    (hcorner : 0 ≤ sharpGap n r x u A v B)
    (hfaceA : sharpGradA n r x u A v B < 0 →
      0 ≤ sharpSideA n r x u A v B → 0 ≤ sharpFaceA n r x u A v B)
    (hfaceB : sharpGradB n r x u A v B < 0 →
      0 ≤ sharpSideB n r x u A v B → 0 ≤ sharpFaceB n r x u A v B)
    (hinterior : sharpSideA n r x u A v B < 0 →
      sharpSideB n r x u A v B < 0 → 0 ≤ sharpInterior n r x u A v B) :
    0 ≤ excursionReducedGap n r x u A C v B D := by
  have hn0 : 0 < n := by linarith
  have hnnonneg : 0 ≤ n := by linarith
  let C0 := sharpThird n u A
  let D0 := sharpThird n v B
  let s := C-C0
  let t := D-D0
  have hs : 0 ≤ s := by
    dsimp [s, C0, sharpThird]
    apply sub_nonneg.mpr
    rw [div_le_iff₀ (by positivity : 0 < n*u)]
    nlinarith [hC]
  have ht : 0 ≤ t := by
    dsimp [t, D0, sharpThird]
    apply sub_nonneg.mpr
    rw [div_le_iff₀ (by positivity : 0 < n*v)]
    nlinarith [hD]
  have hkkt := excursionReducedGap_quadrant_nonneg n r x u A C0 v B D0 s t
    hnnonneg hr hx hu hA hv hB hs ht
    (by simpa [C0, D0, sharpGap] using hcorner)
    (by simpa [C0, D0, sharpGradA, sharpGradB, sharpSideA,
        sharpFaceA, sharpGap] using hfaceA)
    (by simpa [C0, D0, sharpGradA, sharpGradB, sharpSideB,
        sharpFaceB, sharpGap] using hfaceB)
    (by simpa [C0, D0, sharpGradA, sharpGradB, sharpSideA, sharpSideB,
        sharpInterior, sharpGap] using hinterior)
  have hCeq : C0+s = C := by dsimp [s]; ring
  have hDeq : D0+t = D := by dsimp [t]; ring
  rwa [hCeq, hDeq] at hkkt

/-- Uniform KKT reduction with the interior alternative discharged.  Thus the
general induction step now needs only the sharp corner and the two one-face
certificates. -/
theorem excursionReducedGap_nonneg_of_corner_faces
    (n r x u A C v B D : ℝ)
    (hn : 4 ≤ n) (hr : 0 < r) (hx : 0 ≤ x)
    (hu : 0 < u) (hv : 0 < v)
    (hA : n*u^2 ≤ (n-1)*A) (hB : n*v^2 ≤ (n-1)*B)
    (hC : (n+1)*A^2 ≤ n*u*C) (hD : (n+1)*B^2 ≤ n*v*D)
    (hcorner : 0 ≤ sharpGap n r x u A v B)
    (hfaceA : sharpGradA n r x u A v B < 0 →
      0 ≤ sharpSideA n r x u A v B → 0 ≤ sharpFaceA n r x u A v B)
    (hfaceB : sharpGradB n r x u A v B < 0 →
      0 ≤ sharpSideB n r x u A v B → 0 ≤ sharpFaceB n r x u A v B) :
    0 ≤ excursionReducedGap n r x u A C v B D := by
  have hAp : 0 < A := by nlinarith [sq_pos_of_pos hu]
  have hBp : 0 < B := by nlinarith [sq_pos_of_pos hv]
  apply excursionReducedGap_nonneg_of_sharp_certificates
    n r x u A C v B D (by linarith) hr hx hu hAp hv hBp hC hD
    hcorner hfaceA hfaceB
  intro hsideA hsideB
  exact (sharpSides_interior_impossible n r x u A v B hn hr hx hu hv
    hA hB hsideA hsideB).elim

/-- In mixture coordinates, the complete third-moment induction step is reduced
to three scale-free semialgebraic certificates: the sharp corner and the two
conditional face discriminants.  The interior KKT alternative has already been
eliminated uniformly above. -/
theorem excursionReducedGap_mixture_coordinates_nonneg_of_uniform_certificates
    (n a T Y p q C D : ℝ)
    (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hp : 0 < p) (hp1 : p ≤ 1)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hC : (n+1)*(n*p*Y^2/(n-1))^2 ≤ n*(p*Y)*C)
    (hD : (n+1)*(n*q*T^2/(n-1))^2 ≤ n*(q*T)*D)
    (hcorner : 0 ≤ uniformSharpGap n a T Y q)
    (hfaceA : uniformGradA n a T Y q < 0 →
      uniformReturnSide n a T Y q ≤ 0 →
      0 ≤ uniformSharpFaceA n a T Y q)
    (hfaceB : 0 < uniformGradB n a T Y q →
      0 ≤ uniformTerminalSide n a T Y q →
      0 ≤ uniformSharpFaceB n a T Y q) :
    0 ≤ excursionReducedGap n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) C (q*T) (n*q*T^2/(n-1)) D := by
  have hsecondA : n*(p*Y)^2 ≤ (n-1)*(n*p*Y^2/(n-1)) := by
    have hn1 : n-1 ≠ 0 := by linarith
    field_simp [hn1]
    nlinarith [mul_nonneg (sq_nonneg Y) (sub_nonneg.mpr hp1)]
  have hsecondB : n*(q*T)^2 ≤ (n-1)*(n*q*T^2/(n-1)) := by
    have hn1 : n-1 ≠ 0 := by linarith
    field_simp [hn1]
    nlinarith [mul_nonneg (sq_nonneg T) (sub_nonneg.mpr hq1)]
  apply excursionReducedGap_nonneg_of_corner_faces
    n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) C (q*T) (n*q*T^2/(n-1)) D
      hn (by positivity) (by positivity) (by positivity) (by positivity)
      hsecondA hsecondB hC hD
  · exact sharpGap_nonneg_of_uniform n a T Y p q hn ha hT hY hp hq hcorner
  · exact sharpFaceA_nonneg_of_uniform n a T Y p q hn ha hT hY hp hq hfaceA
  · exact sharpFaceB_nonneg_of_uniform n a T Y p q hn ha hT hY hp hq hfaceB

/-- The same reduction after discharging the sharp corner uniformly.  Only
the two conditional one-face certificates remain. -/
theorem excursionReducedGap_mixture_coordinates_nonneg_of_uniform_faces
    (n a T Y p q C D : ℝ)
    (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hp : 0 < p) (hp1 : p ≤ 1)
    (hq : 0 < q) (hq1 : q ≤ 1)
    (hC : (n+1)*(n*p*Y^2/(n-1))^2 ≤ n*(p*Y)*C)
    (hD : (n+1)*(n*q*T^2/(n-1))^2 ≤ n*(q*T)*D)
    (hfaceA : uniformGradA n a T Y q < 0 →
      uniformReturnSide n a T Y q ≤ 0 →
      0 ≤ uniformSharpFaceA n a T Y q)
    (hfaceB : 0 < uniformGradB n a T Y q →
      0 ≤ uniformTerminalSide n a T Y q →
      0 ≤ uniformSharpFaceB n a T Y q) :
    0 ≤ excursionReducedGap n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) C (q*T) (n*q*T^2/(n-1)) D := by
  apply excursionReducedGap_mixture_coordinates_nonneg_of_uniform_certificates
    n a T Y p q C D hn ha ha1 hT hY hp hp1 hq hq1 hC hD
  · exact uniformSharpGap_nonneg n a T Y q hn ha.le ha1 hT hY hq hq1
  · exact hfaceA
  · exact hfaceB

/-! ## Compatibility with the completed four-stage calculation -/

theorem stageGap_four
    (r a1 a2 a3 a4 b1 b2 b3 b4 : ℝ) :
    stageGap 4 r a1 a2 a3 a4 b1 b2 b3 b4 =
      geomGap r a1 a2 a3 a4 b1 b2 b3 b4 := by
  unfold stageGap geomGap
  norm_num

theorem excursionReducedGap_four
    (r x u A C v B D : ℝ) :
    excursionReducedGap 4 r x u A C v B D =
      SSP.K3S4ExcursionKKT.excursionReducedGap r x u A C v B D := by
  unfold excursionReducedGap SSP.K3S4ExcursionKKT.excursionReducedGap
  rw [stageGap_four]
  norm_num

theorem excursionHessian_four
    (r x u A v B : ℝ) :
    excursionHAA 4 r x u A v B = SSP.K3S4ExcursionKKT.excursionHAA r x u A v B ∧
    excursionHAB 4 r = SSP.K3S4ExcursionKKT.excursionHAB r ∧
    excursionHBB 4 r x u A v B = SSP.K3S4ExcursionKKT.excursionHBB r x u A v B := by
  unfold excursionHAA excursionHAB excursionHBB hessianCore
  unfold SSP.K3S4ExcursionKKT.excursionHAA SSP.K3S4ExcursionKKT.excursionHAB
    SSP.K3S4ExcursionKKT.excursionHBB
  norm_num
  constructor <;> ring

end SSP.K3AllStages
