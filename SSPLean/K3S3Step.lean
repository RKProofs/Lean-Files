import SSPLean.K3S3TerminalFace

/-!
# The complete scalar renewal step at `k = 3`, `n = 3`

This file transports the three exceptional normalized certificates back to
arbitrary renewal coordinates and applies the general two-variable KKT lemma.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

open SSP.K3S4Renewal SSP.K3S4KKT

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem sharpGradA_three_scale
    (L r x u A v B : ℝ) (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    sharpGradA 3 r (L*x) (L*u) (L^2*A) (L*v) (L^2*B) =
      L^3*sharpGradA 3 r x u A v B := by
  unfold sharpGradA sharpThird excursionGradA excursionHAA excursionReducedGap
  unfold stageGap hessianCore geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4
  field_simp [hL, hu, hv, hA, hB]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem sharpGradB_three_scale
    (L r x u A v B : ℝ) (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    sharpGradB 3 r (L*x) (L*u) (L^2*A) (L*v) (L^2*B) =
      L^3*sharpGradB 3 r x u A v B := by
  unfold sharpGradB sharpThird excursionGradB excursionHBB excursionReducedGap
  unfold stageGap hessianCore geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4
  field_simp [hL, hu, hv, hA, hB]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem sharpSideA_three_scale
    (L r x u A v B : ℝ) (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    sharpSideA 3 r (L*x) (L*u) (L^2*A) (L*v) (L^2*B) =
      L^3*sharpSideA 3 r x u A v B := by
  unfold sharpSideA
  rw [sharpGradA_three_scale L r x u A v B hL hu hv hA hB,
    sharpGradB_three_scale L r x u A v B hL hu hv hA hB]
  unfold excursionHAA excursionHAB hessianCore
  field_simp [hL, hA, hB]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem sharpSideB_three_scale
    (L r x u A v B : ℝ) (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    sharpSideB 3 r (L*x) (L*u) (L^2*A) (L*v) (L^2*B) =
      L^3*sharpSideB 3 r x u A v B := by
  unfold sharpSideB
  rw [sharpGradA_three_scale L r x u A v B hL hu hv hA hB,
    sharpGradB_three_scale L r x u A v B hL hu hv hA hB]
  unfold excursionHBB excursionHAB hessianCore
  field_simp [hL, hA, hB]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem sharpFaceA_three_scale
    (L r x u A v B : ℝ) (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    sharpFaceA 3 r (L*x) (L*u) (L^2*A) (L*v) (L^2*B) =
      L^6*sharpFaceA 3 r x u A v B := by
  unfold sharpFaceA
  rw [sharpGap_three_scale L r x u A v B hL hu hv hA hB,
    sharpGradA_three_scale L r x u A v B hL hu hv hA hB]
  unfold excursionHAA hessianCore
  field_simp [hL, hA, hB]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem sharpFaceB_three_scale
    (L r x u A v B : ℝ) (hL : L ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    sharpFaceB 3 r (L*x) (L*u) (L^2*A) (L*v) (L^2*B) =
      L^6*sharpFaceB 3 r x u A v B := by
  unfold sharpFaceB
  rw [sharpGap_three_scale L r x u A v B hL hu hv hA hB,
    sharpGradB_three_scale L r x u A v B hL hu hv hA hB]
  unfold excursionHBB hessianCore
  field_simp [hL, hA, hB]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem sharpGradA_three_mixture
    (a T Y p q : ℝ) (hT : T ≠ 0) (hY : Y ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hsum : p*Y+a ≠ 0) :
    sharpGradA 3 (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) =
      a*uniformGradA 3 a T Y q/(2*Y*p) := by
  unfold sharpGradA sharpThird excursionGradA excursionHAA
  unfold excursionReducedGap stageGap hessianCore
  unfold geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4 uniformGradA
  have hsq : a*Y*p*2+a^2+Y^2*p^2 ≠ 0 := by
    convert pow_ne_zero 2 hsum using 1
    all_goals ring
  field_simp [hT, hY, hp, hq, hsum, hsq]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem sharpGradB_three_mixture
    (a T Y p q : ℝ) (hT : T ≠ 0) (hY : Y ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hsum : p*Y+a ≠ 0) :
    sharpGradB 3 (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) =
      -uniformGradB 3 a T Y q/2 := by
  unfold sharpGradB sharpThird excursionGradB excursionHBB
  unfold excursionReducedGap stageGap hessianCore
  unfold geomM4 geomM3 geomM2 geomM1
  unfold kernelM1 kernelM2 kernelM3 kernelM4 uniformGradB
  have hsq : a*Y*p*2+a^2+Y^2*p^2 ≠ 0 := by
    convert pow_ne_zero 2 hsum using 1
    all_goals ring
  field_simp [hT, hY, hp, hq, hsum, hsq]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem excursionHAA_three_mixture
    (a T Y p q : ℝ) (hY : Y ≠ 0) (hp : p ≠ 0)
    (hsum : p*Y+a ≠ 0) :
    excursionHAA 3 (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) =
      a*uniformHAA 3 a T Y q/(6*Y^3*p^2) := by
  unfold excursionHAA hessianCore uniformHAA
  have hsq : a*Y*p*2+a^2+Y^2*p^2 ≠ 0 := by
    convert pow_ne_zero 2 hsum using 1
    all_goals ring
  field_simp [hY, hp, hsum, hsq]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem excursionHBB_three_mixture
    (a T Y p q : ℝ) (hT : T ≠ 0) (hY : Y ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hsum : p*Y+a ≠ 0) :
    excursionHBB 3 (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) =
      uniformHBB 3 a T Y q/(6*T^2*q) := by
  unfold excursionHBB hessianCore uniformHBB
  have hsq : a*Y*p*2+a^2+Y^2*p^2 ≠ 0 := by
    convert pow_ne_zero 2 hsum using 1
    all_goals ring
  field_simp [hT, hY, hp, hq, hsum, hsq]
  ring

private theorem uniform_sideA_three_identity (a T Y q : ℝ) :
    uniformHAA 3 a T Y q*uniformGradB 3 a T Y q
        -72*a*Y*uniformGradA 3 a T Y q =
      5*uniformSideFactor 3 a T Y q*uniformReturnSide 3 a T Y q := by
  unfold uniformHAA uniformGradA uniformGradB uniformSideFactor
  unfold uniformReturnSide uniformReturnM uniformReturnK
  ring

private theorem uniform_sideB_three_identity (a T Y q : ℝ) :
    uniformHBB 3 a T Y q*uniformGradA 3 a T Y q
        -72*uniformGradB 3 a T Y q*T^2*q =
      5*uniformSideFactor 3 a T Y q*uniformTerminalSide 3 a T Y q := by
  unfold uniformHBB uniformGradA uniformGradB uniformSideFactor
  unfold uniformTerminalSide uniformTerminalL uniformTerminalS0
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem sharpSideA_three_mixture
    (a T Y p q : ℝ) (hT : T ≠ 0) (hY : Y ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hsum : p*Y+a ≠ 0) :
    48*Y^3*p^2*sharpSideA 3 (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) =
      -20*a*uniformSideFactor 3 a T Y q*uniformReturnSide 3 a T Y q := by
  unfold sharpSideA
  rw [sharpGradA_three_mixture a T Y p q hT hY hp hq hsum,
    sharpGradB_three_mixture a T Y p q hT hY hp hq hsum,
    excursionHAA_three_mixture a T Y p q hY hp hsum]
  unfold excursionHAB
  field_simp [hT, hY, hp, hq]
  linear_combination -48*a*uniform_sideA_three_identity a T Y q

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem sharpSideB_three_mixture
    (a T Y p q : ℝ) (hT : T ≠ 0) (hY : Y ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hsum : p*Y+a ≠ 0) :
    48*T^2*Y*p*q*sharpSideB 3 (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) =
      20*a*uniformSideFactor 3 a T Y q*uniformTerminalSide 3 a T Y q := by
  unfold sharpSideB
  rw [sharpGradA_three_mixture a T Y p q hT hY hp hq hsum,
    sharpGradB_three_mixture a T Y p q hT hY hp hq hsum,
    excursionHBB_three_mixture a T Y p q hT hY hp hq hsum]
  unfold excursionHAB
  field_simp [hT, hY, hp, hq]
  linear_combination 48*a*uniform_sideB_three_identity a T Y q

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem sharpFaceA_three_mixture
    (a T Y p q : ℝ) (hT : T ≠ 0) (hY : Y ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hsum : p*Y+a ≠ 0)
    (hsum1 : Y+a ≠ 0) :
    p^2*sharpFaceA 3 (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) =
      uniformSharpFaceA 3 a T Y q := by
  have hgap1 := sharpGap_three_mixture_coordinates a T Y 1 q hT hY
    (by norm_num) hq (by simpa using hsum1) hsum1
  have hgrad1 := sharpGradA_three_mixture a T Y 1 q hT hY
    (by norm_num) hq (by simpa using hsum1)
  have hhaa1 := excursionHAA_three_mixture a T Y 1 q hY
    (by norm_num) (by simpa using hsum1)
  norm_num at hgap1 hgrad1 hhaa1
  unfold uniformSharpFaceA sharpFaceA
  norm_num
  rw [sharpGap_three_mixture_coordinates a T Y p q hT hY hp hq hsum hsum1,
    sharpGradA_three_mixture a T Y p q hT hY hp hq hsum,
    excursionHAA_three_mixture a T Y p q hY hp hsum,
    hgap1, hgrad1, hhaa1]
  field_simp [hY, hp]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem sharpFaceB_three_mixture
    (a T Y p q : ℝ) (hT : T ≠ 0) (hY : Y ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hsum : p*Y+a ≠ 0)
    (hsum1 : Y+a ≠ 0) :
    sharpFaceB 3 (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) =
      uniformSharpFaceB 3 a T Y q := by
  have hgap1 := sharpGap_three_mixture_coordinates a T Y 1 q hT hY
    (by norm_num) hq (by simpa using hsum1) hsum1
  have hgrad1 := sharpGradB_three_mixture a T Y 1 q hT hY
    (by norm_num) hq (by simpa using hsum1)
  have hhbb1 := excursionHBB_three_mixture a T Y 1 q hT hY
    (by norm_num) hq (by simpa using hsum1)
  norm_num at hgap1 hgrad1 hhbb1
  unfold uniformSharpFaceB sharpFaceB
  norm_num
  rw [sharpGap_three_mixture_coordinates a T Y p q hT hY hp hq hsum hsum1,
    sharpGradB_three_mixture a T Y p q hT hY hp hq hsum,
    excursionHBB_three_mixture a T Y p q hT hY hp hq hsum,
    hgap1, hgrad1, hhbb1]

private theorem three_mixture_coordinates_exist
    (r x u A v B : ℝ) (hr : 0 < r) (hx : 0 ≤ x)
    (hu : 0 < u) (hv : 0 < v)
    (hA : 3*u^2 ≤ 2*A) (hB : 3*v^2 ≤ 2*B) :
    ∃ a T Y p q L : ℝ,
      0 < a ∧ a ≤ 1 ∧ 0 < T ∧ 0 < Y ∧ 0 < p ∧ p ≤ 1 ∧
      0 < q ∧ q ≤ 1 ∧ 0 < L ∧
      a/(p*Y)=r ∧
      L*(p*Y*(1-a)/(p*Y+a))=x ∧
      L*(p*Y)=u ∧ L^2*(3*p*Y^2/2)=A ∧
      L*(q*T)=v ∧ L^2*(3*q*T^2/2)=B := by
  have hAp : 0 < A := by nlinarith [sq_pos_of_pos hu]
  have hBp : 0 < B := by nlinarith [sq_pos_of_pos hv]
  let p := mixtureWeight 3 u A
  let q := mixtureWeight 3 v B
  let L := r*u+(r+1)*x
  obtain ⟨hp, hp1⟩ := mixtureWeight_pos_le_one 3 u A (by norm_num) hu (by
    norm_num at hA ⊢
    exact hA)
  obtain ⟨hq, hq1⟩ := mixtureWeight_pos_le_one 3 v B (by norm_num) hv (by
    norm_num at hB ⊢
    exact hB)
  have hp' : 0 < p := by simpa [p] using hp
  have hq' : 0 < q := by simpa [q] using hq
  have hp1' : p ≤ 1 := by simpa [p] using hp1
  have hq1' : q ≤ 1 := by simpa [q] using hq1
  have hL : 0 < L := by
    dsimp [L]
    have : 0 < r*u := mul_pos hr hu
    positivity
  let a := r*u/L
  let Y := u/(p*L)
  let T := v/(q*L)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [div_le_one hL]
    dsimp [L]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r+1) hx]
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨a, T, Y, p, q, L, ha, ha1, hT, hY, hp', hp1', hq', hq1', hL,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [a, Y]
    field_simp [hp'.ne', hL.ne', hu.ne']
  · dsimp [a, Y, L]
    field_simp [hp'.ne', hL.ne', hu.ne']
    simp
    ring
  · dsimp [Y]
    field_simp [hp'.ne', hL.ne']
  · dsimp [Y, p, mixtureWeight]
    norm_num
    field_simp [hu.ne', hAp.ne', hL.ne']
  · dsimp [T]
    field_simp [hq'.ne', hL.ne']
  · dsimp [T, q, mixtureWeight]
    field_simp [hv.ne', hBp.ne', hL.ne']
    ring

private theorem sharpFaceA_three_nonneg_general
    (r x u A v B : ℝ) (hr : 0 < r) (hx : 0 ≤ x)
    (hu : 0 < u) (hv : 0 < v)
    (hA : 3*u^2 ≤ 2*A) (hB : 3*v^2 ≤ 2*B) :
    0 ≤ sharpFaceA 3 r x u A v B := by
  obtain ⟨a, T, Y, p, q, L, ha, ha1, hT, hY, hp, hp1, hq, hq1, hL,
    hrid, hxid, huid, hAid, hvid, hBid⟩ :=
    three_mixture_coordinates_exist r x u A v B hr hx hu hv hA hB
  have hpY : p*Y ≠ 0 := by positivity
  have hqT : q*T ≠ 0 := by positivity
  have hAc : 3*p*Y^2/2 ≠ 0 := by positivity
  have hBc : 3*q*T^2/2 ≠ 0 := by positivity
  have hU := uniformSharpFaceA_three_nonneg a T Y q ha hT hY hq hq1
  have hmix := sharpFaceA_three_mixture a T Y p q hT.ne' hY.ne' hp.ne' hq.ne'
    (by positivity) (by positivity)
  have hnorm : 0 ≤ sharpFaceA 3 (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) := by
    have hs : 0 ≤ p^2*sharpFaceA 3 (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) := by
      rw [hmix]
      exact hU
    exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos hp)).mp hs
  rw [hrid] at hnorm
  have hscale := sharpFaceA_three_scale L (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
    (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2)
    hL.ne' hpY hqT hAc hBc
  rw [hrid, hxid, huid, hAid, hvid, hBid] at hscale
  rw [hscale]
  exact mul_nonneg (by positivity) hnorm

private theorem sharpFaceB_three_nonneg_general
    (r x u A v B : ℝ) (hr : 0 < r) (hx : 0 ≤ x)
    (hu : 0 < u) (hv : 0 < v)
    (hA : 3*u^2 ≤ 2*A) (hB : 3*v^2 ≤ 2*B)
    (hgrad : sharpGradB 3 r x u A v B < 0)
    (hside : 0 ≤ sharpSideB 3 r x u A v B) :
    0 ≤ sharpFaceB 3 r x u A v B := by
  obtain ⟨a, T, Y, p, q, L, ha, ha1, hT, hY, hp, hp1, hq, hq1, hL,
    hrid, hxid, huid, hAid, hvid, hBid⟩ :=
    three_mixture_coordinates_exist r x u A v B hr hx hu hv hA hB
  have hpY : p*Y ≠ 0 := by positivity
  have hqT : q*T ≠ 0 := by positivity
  have hAc : 3*p*Y^2/2 ≠ 0 := by positivity
  have hBc : 3*q*T^2/2 ≠ 0 := by positivity
  have hgB := sharpGradB_three_scale L (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
    (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2)
    hL.ne' hpY hqT hAc hBc
  have hsB := sharpSideB_three_scale L (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
    (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2)
    hL.ne' hpY hqT hAc hBc
  have hfB := sharpFaceB_three_scale L (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
    (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2)
    hL.ne' hpY hqT hAc hBc
  rw [hrid, hxid, huid, hAid, hvid, hBid] at hgB hsB hfB
  have hL3 : 0 < L^3 := by positivity
  have hgradM : sharpGradB 3 r (p*Y*(1-a)/(p*Y+a))
      (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) < 0 := by
    rw [hgB] at hgrad
    by_contra hn
    exact absurd hgrad (not_lt.mpr (mul_nonneg hL3.le (not_lt.mp hn)))
  have hsideM : 0 ≤ sharpSideB 3 r (p*Y*(1-a)/(p*Y+a))
      (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) := by
    rw [hsB] at hside
    exact nonneg_of_mul_nonneg_right hside hL3
  have hgradId := sharpGradB_three_mixture a T Y p q
    hT.ne' hY.ne' hp.ne' hq.ne' (by positivity)
  have hgradU : 0 < uniformGradB 3 a T Y q := by
    rw [← hrid, hgradId] at hgradM
    by_contra hn
    have hu0 : uniformGradB 3 a T Y q ≤ 0 := le_of_not_gt hn
    have : 0 ≤ -2*uniformGradB 3 a T Y q/2^2 := by nlinarith
    linarith
  have hsideId := sharpSideB_three_mixture a T Y p q
    hT.ne' hY.ne' hp.ne' hq.ne' (by positivity)
  have hterminal : 0 ≤ uniformTerminalSide 3 a T Y q := by
    have hden : 0 < 48*T^2*Y*p*q := by positivity
    have hs : 0 ≤ 48*T^2*Y*p*q*
        sharpSideB 3 (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) := by
      rw [hrid]
      exact mul_nonneg hden.le hsideM
    rw [hsideId] at hs
    have hfactor : 0 < uniformSideFactor 3 a T Y q := by
      rw [show uniformSideFactor 3 a T Y q =
          3*T^2*q+4*T*q+3*a*Y+4 by unfold uniformSideFactor; ring]
      positivity
    nlinarith [mul_pos ha (mul_pos hfactor (by norm_num : (0:ℝ)<20))]
  have hU := uniformSharpFaceB_three_nonneg a T Y q ha ha1 hT hY hq hq1
    hgradU hterminal
  have hmix := sharpFaceB_three_mixture a T Y p q hT.ne' hY.ne' hp.ne' hq.ne'
    (by positivity) (by positivity)
  have hnorm : 0 ≤ sharpFaceB 3 r (p*Y*(1-a)/(p*Y+a))
      (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) := by
    rw [← hrid, hmix]
    exact hU
  rw [hfB]
  exact mul_nonneg (by positivity) hnorm

private theorem sharpSides_three_interior_impossible
    (r x u A v B : ℝ) (hr : 0 < r) (hx : 0 ≤ x)
    (hu : 0 < u) (hv : 0 < v)
    (hA : 3*u^2 ≤ 2*A) (hB : 3*v^2 ≤ 2*B)
    (hsideA : sharpSideA 3 r x u A v B < 0)
    (hsideB : sharpSideB 3 r x u A v B < 0) : False := by
  obtain ⟨a, T, Y, p, q, L, ha, ha1, hT, hY, hp, hp1, hq, hq1, hL,
    hrid, hxid, huid, hAid, hvid, hBid⟩ :=
    three_mixture_coordinates_exist r x u A v B hr hx hu hv hA hB
  have hpY : p*Y ≠ 0 := by positivity
  have hqT : q*T ≠ 0 := by positivity
  have hAc : 3*p*Y^2/2 ≠ 0 := by positivity
  have hBc : 3*q*T^2/2 ≠ 0 := by positivity
  have hsA := sharpSideA_three_scale L (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
    (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2)
    hL.ne' hpY hqT hAc hBc
  have hsB := sharpSideB_three_scale L (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
    (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2)
    hL.ne' hpY hqT hAc hBc
  rw [hrid, hxid, huid, hAid, hvid, hBid] at hsA hsB
  have hL3 : 0 < L^3 := by positivity
  have hsideAN : sharpSideA 3 (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) < 0 := by
    rw [hrid]
    rw [hsA] at hsideA
    by_contra hn
    exact absurd hsideA (not_lt.mpr (mul_nonneg hL3.le (not_lt.mp hn)))
  have hsideBN : sharpSideB 3 (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) < 0 := by
    rw [hrid]
    rw [hsB] at hsideB
    by_contra hn
    exact absurd hsideB (not_lt.mpr (mul_nonneg hL3.le (not_lt.mp hn)))
  have hfactor : 0 < uniformSideFactor 3 a T Y q := by
    rw [show uniformSideFactor 3 a T Y q =
        3*T^2*q+4*T*q+3*a*Y+4 by unfold uniformSideFactor; ring]
    positivity
  have hsideAid := sharpSideA_three_mixture a T Y p q
    hT.ne' hY.ne' hp.ne' hq.ne' (by positivity)
  have hscaledA : 48*Y^3*p^2*sharpSideA 3 (a/(p*Y))
      (p*Y*(1-a)/(p*Y+a)) (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) < 0 := by
    exact mul_neg_of_pos_of_neg (by positivity) hsideAN
  rw [hsideAid] at hscaledA
  have hreturn : 0 < uniformReturnSide 3 a T Y q := by
    have hc : 0 < 20*a*uniformSideFactor 3 a T Y q := by positivity
    nlinarith
  have hterminal := uniformTerminalSide_three_nonneg_of_returnSide_pos
    a T Y q ha ha1 hT hY hq hreturn
  have hsideBid := sharpSideB_three_mixture a T Y p q
    hT.ne' hY.ne' hp.ne' hq.ne' (by positivity)
  have hscaledB : 48*T^2*Y*p*q*sharpSideB 3 (a/(p*Y))
      (p*Y*(1-a)/(p*Y+a)) (p*Y) (3*p*Y^2/2) (q*T) (3*q*T^2/2) < 0 := by
    exact mul_neg_of_pos_of_neg (by positivity) hsideBN
  rw [hsideBid] at hscaledB
  have hc : 0 < 20*a*uniformSideFactor 3 a T Y q := by positivity
  nlinarith

private theorem excursionReducedGap_three_of_sharp_certificates
    (r x u A C v B D : ℝ)
    (hr : 0 < r) (hx : 0 ≤ x)
    (hu : 0 < u) (hA : 0 < A) (hv : 0 < v) (hB : 0 < B)
    (hC : 4*A^2 ≤ 3*u*C) (hD : 4*B^2 ≤ 3*v*D)
    (hcorner : 0 ≤ sharpGap 3 r x u A v B)
    (hfaceA : sharpGradA 3 r x u A v B < 0 →
      0 ≤ sharpSideA 3 r x u A v B → 0 ≤ sharpFaceA 3 r x u A v B)
    (hfaceB : sharpGradB 3 r x u A v B < 0 →
      0 ≤ sharpSideB 3 r x u A v B → 0 ≤ sharpFaceB 3 r x u A v B)
    (hinterior : sharpSideA 3 r x u A v B < 0 →
      sharpSideB 3 r x u A v B < 0 → 0 ≤ sharpInterior 3 r x u A v B) :
    0 ≤ excursionReducedGap 3 r x u A C v B D := by
  let C0 := sharpThird 3 u A
  let D0 := sharpThird 3 v B
  let s := C-C0
  let t := D-D0
  have hs : 0 ≤ s := by
    dsimp [s, C0, sharpThird]
    apply sub_nonneg.mpr
    rw [div_le_iff₀ (by positivity : 0 < 3*u)]
    nlinarith
  have ht : 0 ≤ t := by
    dsimp [t, D0, sharpThird]
    apply sub_nonneg.mpr
    rw [div_le_iff₀ (by positivity : 0 < 3*v)]
    nlinarith
  have hkkt := excursionReducedGap_quadrant_nonneg 3 r x u A C0 v B D0 s t
    (by norm_num) hr hx hu hA hv hB hs ht
    (by simpa [C0, D0, sharpGap] using hcorner)
    (by simpa [C0, D0, sharpGradA, sharpGradB, sharpSideA,
        sharpFaceA, sharpGap] using hfaceA)
    (by simpa [C0, D0, sharpGradA, sharpGradB, sharpSideB,
        sharpFaceB, sharpGap] using hfaceB)
    (by simpa [C0, D0, sharpGradA, sharpGradB, sharpSideA, sharpSideB,
        sharpInterior, sharpGap] using hinterior)
  have hCeq : C0+s=C := by dsimp [s]; ring
  have hDeq : D0+t=D := by dsimp [t]; ring
  rwa [hCeq, hDeq] at hkkt

/-- The complete lowered-fourth-moment KKT inequality for `n = 3`. -/
theorem excursionReducedGap_three_nonneg_general
    (r x u A C v B D : ℝ)
    (hr : 0 < r) (hx : 0 ≤ x) (hu : 0 < u) (hv : 0 < v)
    (hA : 3*u^2 ≤ 2*A) (hB : 3*v^2 ≤ 2*B)
    (hC : 4*A^2 ≤ 3*u*C) (hD : 4*B^2 ≤ 3*v*D) :
    0 ≤ excursionReducedGap 3 r x u A C v B D := by
  apply excursionReducedGap_three_of_sharp_certificates
    r x u A C v B D hr hx hu
    (by nlinarith [sq_pos_of_pos hu]) hv (by nlinarith [sq_pos_of_pos hv]) hC hD
  · exact sharpGap_three_nonneg_general r x u A v B hr hx hu hv hA hB
  · intro _ _
    exact sharpFaceA_three_nonneg_general r x u A v B hr hx hu hv hA hB
  · intro hgrad hside
    exact sharpFaceB_three_nonneg_general r x u A v B hr hx hu hv hA hB hgrad hside
  · intro hsideA hsideB
    exact (sharpSides_three_interior_impossible r x u A v B hr hx hu hv hA hB
      hsideA hsideB).elim

/-- The full scalar renewal step at the exceptional parent order `n = 3`. -/
theorem k3_renewal_step_three
    (r x u A C E v B D F : ℝ)
    (hr : 0 < r) (hx : 0 ≤ x) (hu : 0 < u) (hv : 0 < v)
    (hA : 3*u^2 ≤ 2*A) (hB : 3*v^2 ≤ 2*B)
    (hC : 4*A^2 ≤ 3*u*C) (hD : 4*B^2 ≤ 3*v*D)
    (hE : 5*C^2 ≤ 4*A*E) (hF : 5*D^2 ≤ 4*B*F) :
    0 ≤ stageGap 3 r
      (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C) (kernelM4 x u A C E)
      (kernelM1 x v) (kernelM2 x v B) (kernelM3 x v B D)
        (kernelM4 x v B D F) := by
  have hAp : 0 < A := by nlinarith [sq_pos_of_pos hu]
  have hBp : 0 < B := by nlinarith [sq_pos_of_pos hv]
  have hEle : 5*C^2/(4*A) ≤ E := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hE]
  have hFle : 5*D^2/(4*B) ≤ F := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hF]
  have hmono := stageGap_fourth_mono 3 r
    (kernelM1 x u) (kernelM2 x u A) (kernelM3 x u A C)
    (kernelM4 x u A C E) (kernelM4 x u A C (5*C^2/(4*A)))
    (kernelM1 x v) (kernelM2 x v B) (kernelM3 x v B D)
    (kernelM4 x v B D F) (kernelM4 x v B D (5*D^2/(4*B)))
    (by norm_num) hr.le (by unfold kernelM1; linarith)
    (by unfold kernelM2; nlinarith [sq_nonneg x, mul_nonneg hx hu.le])
    (by unfold kernelM1; linarith)
    (by unfold kernelM2; nlinarith [sq_nonneg x, mul_nonneg hx hv.le])
    (by unfold kernelM4; linarith) (by unfold kernelM4; linarith)
  have hgap := excursionReducedGap_three_nonneg_general
    r x u A C v B D hr hx hu hv hA hB hC hD
  unfold excursionReducedGap at hgap
  norm_num at hgap
  linarith [hmono, hgap]

end SSP.K3AllStages
