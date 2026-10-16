import SSPLean.K3CyclicRealMiddle

/-! # Constructing the real or complex root data of a canonical cubic -/

set_option autoImplicit false
open Set

namespace SSP.K3Cyclic

/-- The two root-data cases consumed by the analytic canonical proofs. -/
def CanonicalSpectralData (a b Q : ℝ) : Prop :=
  (∃ u v w : ℝ, u ≤ v ∧ v ≤ w ∧ 0 < w ∧
    u+v+w = a+b ∧ u*v+u*w+v*w = a*b ∧ u*v*w = Q) ∨
  (∃ mu d omega : ℝ, 0 < d ∧ omega ≠ 0 ∧
    a+b = 3*mu+d ∧ a*b = 3*mu^2+2*mu*d+d^2*omega^2 ∧
    Q = (mu+d)*(mu^2+d^2*omega^2))

theorem exists_canonical_largest_root {a b Q : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hQ : 0 < Q) :
    ∃ w : ℝ, b < w ∧ w*(w-a)*(w-b) = Q := by
  let R := a+b+Q+1
  let P := fun s : ℝ => s*(s-a)*(s-b)-Q
  have hb : 0 ≤ b := ha.trans hab
  have hRb : b ≤ R := by dsimp [R]; linarith
  have hR0 : 1 ≤ R := by dsimp [R]; linarith
  have hRa : 1 ≤ R-a := by dsimp [R]; linarith
  have hRb1 : 1 ≤ R-b := by dsimp [R]; linarith
  have hRlarge : Q < R := by dsimp [R]; linarith
  have hprod : R ≤ R*(R-a)*(R-b) := by
    have h1 : R ≤ R*(R-a) := by nlinarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ R*(R-a)) (by linarith : 0 ≤ R-b-1)]
  have hP : 0 ∈ Icc (P b) (P R) := by dsimp [P]; constructor <;> nlinarith
  obtain ⟨w, hw, he⟩ := intermediate_value_Icc hRb (by dsimp [P]; fun_prop) hP
  have heq : w*(w-a)*(w-b) = Q := by dsimp [P] at he; linarith
  refine ⟨w, lt_of_le_of_ne hw.1 ?_, heq⟩
  intro h
  rw [← h] at heq
  nlinarith

theorem canonical_spectralData_of_positive_feedback
    {a b Q : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hQ : 0 < Q) :
    CanonicalSpectralData a b Q := by
  obtain ⟨w, hbw, hroot⟩ := exists_canonical_largest_root ha hab hQ
  have hb : 0 ≤ b := ha.trans hab
  have hw : 0 < w := hb.trans_lt hbw
  let S := a+b-w
  let R := Q/w
  let D := S^2-4*R
  have hR : 0 < R := div_pos hQ hw
  have hRw : R*w = Q := by dsimp [R]; field_simp
  have hRidentity : R = (w-a)*(w-b) := by
    apply (div_eq_iff hw.ne').mpr
    nlinarith [hroot]
  have hpair : R+w*S = a*b := by rw [hRidentity]; dsimp [S]; ring
  have hSw : S < 2*w := by dsimp [S]; linarith
  by_cases hD : 0 ≤ D
  · let z := Real.sqrt D
    let u := (S-z)/2
    let v := (S+z)/2
    have hz : 0 ≤ z := Real.sqrt_nonneg _
    have hzsq : z^2 = D := Real.sq_sqrt hD
    have huv : u ≤ v := by dsimp [u,v]; linarith
    have huvsum : u+v = S := by dsimp [u,v]; ring
    have huvprod : u*v = R := by dsimp [u,v,D] at *; nlinarith [hzsq]
    have hvw : v ≤ w := by
      have hgap : 0 ≤ 2*w-S := by linarith
      have hsq : z^2 ≤ (2*w-S)^2 := by
        rw [hzsq]
        dsimp [D]
        rw [hRidentity]
        dsimp [S]
        nlinarith
      have hzw : z ≤ 2*w-S := by nlinarith [sq_nonneg (z+(2*w-S))]
      dsimp [v]
      linarith
    left
    refine ⟨u,v,w,huv,hvw,hw,?_,?_,?_⟩
    · rw [huvsum]; dsimp [S]; ring
    · nlinarith [huvsum, huvprod, hpair]
    · rw [huvprod, hRw]
  · have hDneg : D < 0 := lt_of_not_ge hD
    let mu := S/2
    let d := w-mu
    let z := Real.sqrt (-D)
    let omega := z/(2*d)
    have hd : 0 < d := by dsimp [d,mu]; linarith
    have hz : 0 < z := Real.sqrt_pos.mpr (neg_pos.mpr hDneg)
    have hzsq : z^2 = -D := Real.sq_sqrt (neg_nonneg.mpr hDneg.le)
    have homega : omega ≠ 0 := (div_pos hz (by positivity : 0 < 2*d)).ne'
    have homegasq : d^2*omega^2 = -D/4 := by
      dsimp [omega]
      field_simp
      nlinarith [hzsq]
    right
    refine ⟨mu,d,omega,hd,homega,?_,?_,?_⟩
    · dsimp [mu,d,S]; ring
    · dsimp [mu,d,D] at *; nlinarith [hpair, homegasq]
    · have hRmu : mu^2+d^2*omega^2 = R := by
        dsimp [mu,D] at *; nlinarith [homegasq]
      rw [hRmu]
      dsimp [d]
      nlinarith [hRw]

theorem canonical_spectralData {a b Q : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hQ : 0 ≤ Q) (hne : 0 < b ∨ 0 < Q) :
    CanonicalSpectralData a b Q := by
  by_cases hQ0 : Q = 0
  · left
    have hb : 0 < b := by rcases hne with h | h; exact h; simp [hQ0] at h
    refine ⟨0,a,b,ha,hab,hb,?_,?_,?_⟩ <;> simp [hQ0]
  · exact canonical_spectralData_of_positive_feedback ha hab
      (lt_of_le_of_ne hQ (Ne.symm hQ0))

end SSP.K3Cyclic
