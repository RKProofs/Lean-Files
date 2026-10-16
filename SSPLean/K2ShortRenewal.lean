import SSPLean.K2ShortQuadratic

/-!
# Normalized renewal step for the shorter `k = 2` proof

The return second moment has no Aldous--Shepp lower bound. Its third-moment
inequality, together with the positive holding time, is sufficient.
-/

set_option autoImplicit false
namespace SSP.K2Short

/-- The paper's normalized moment argument, including `v=0` and `p=0`. -/
theorem normalized_bound (n : ℕ) (hn : 2 ≤ n) (v a B R D M2 M3 : ℝ)
    (hv : 0 ≤ v) (hv1 : v < 1) (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hB : B0 n v ≤ B)
    (hret : (n+1)*a^2 ≤ (n : ℝ)*(1-v)*R)
    (hterm : (n+1)*B^2 ≤ (n : ℝ)*v*D)
    (he2 : M2=2*(1-v)+a+B)
    (he3 : M3=3*(1-v)*M2+3*a+R+D) :
    (n+2)*M2^2 ≤ (n+1)*M3 := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hh : 0 < 1-v := by linarith
  have hret' : (n+1)/n*(a^2/(1-v)) ≤ R := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hn0]
    rw [← mul_div_assoc, div_le_iff₀ hh]
    nlinarith [hret]
  rcases eq_or_lt_of_le hv with hvzero | hvpos
  · have hv0 : v=0 := hvzero.symm
    have hB0 : B=0 := by rw [hv0] at hterm; nlinarith [sq_nonneg B]
    have he : (n+1)*(3*(2+a)+3*a+(n+1)/n*a^2)-(n+2)*(2+a)^2 =
        2*(n-1)*(1+a)+a^2/n := by field_simp; ring
    rw [hv0, hB0] at he2
    rw [hv0] at he3 hret'
    norm_num at he2 he3 hret'
    have hg : 0 ≤ 2*(n-1)*(1+a)+a^2/n := by
      have hn1 : (0 : ℝ) ≤ n-1 := by linarith
      positivity
    have hdiff : 0 ≤ (n+1)*(R-(n+1)/n*a^2) := by
      apply mul_nonneg (by positivity)
      nlinarith [hret']
    rw [he2] at he3 ⊢
    rw [he3]
    nlinarith
  · have hterm' : (n+1)/n*(B^2/v) ≤ D := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hn0]
      rw [← mul_div_assoc, div_le_iff₀ hvpos]
      nlinarith [hterm]
    have hg := quadratic_nonneg n hn v a B hvpos hv1 ha hB
    unfold G at hg
    have hslack : 0 ≤ (n+1)*(R+D-(n+1)/n*(a^2/(1-v)+B^2/v)) := by
      apply mul_nonneg (by positivity)
      nlinarith [hret', hterm']
    rw [he2] at he3 ⊢
    rw [he3]
    nlinarith

/-- Homogeneous form, before normalizing the parent mean. -/
theorem homogeneous_bound (n : ℕ) (hn : 2 ≤ n) (m h v a B R D M2 M3 : ℝ)
    (hm : 0 < m) (hh : 0 < h) (hv : 0 ≤ v) (ha : 0 ≤ a)
    (hD : 0 ≤ D) (hmhv : m=h+v)
    (hB : (n : ℝ)/(n-1)*v^2 ≤ B)
    (hret : (n+1)*a^2 ≤ (n : ℝ)*h*R)
    (hterm : (n+1)*B^2 ≤ (n : ℝ)*v*D)
    (he2 : M2=2*h*m+a+B)
    (he3 : M3=3*h*M2+3*a*m+R+D) :
    (n+2)*M2^2 ≤ (n+1)*m*M3 := by
  have eh : 1-v/m=h/m := by rw [hmhv]; field_simp; ring
  have hv1 : v/m < 1 := by rw [div_lt_one hm]; linarith
  have hb : B0 n (v/m) ≤ B/m^2 := by
    unfold B0
    have he : (n : ℝ)/(n-1)*(v/m)^2 = ((n : ℝ)/(n-1)*v^2)/m^2 := by ring
    rw [he]
    exact div_le_div_of_nonneg_right hB (sq_nonneg m)
  have hr : (n+1)*(a/m^2)^2 ≤ (n : ℝ)*(1-v/m)*(R/m^3) := by
    rw [eh]
    have he1 : (n+1)*(a/m^2)^2 = ((n+1)*a^2)/m^4 := by ring
    have he2 : (n : ℝ)*(h/m)*(R/m^3) = ((n : ℝ)*h*R)/m^4 := by ring
    rw [he1, he2]
    exact div_le_div_of_nonneg_right hret (by positivity)
  have hd : (n+1)*(B/m^2)^2 ≤ (n : ℝ)*(v/m)*(D/m^3) := by
    have he1 : (n+1)*(B/m^2)^2 = ((n+1)*B^2)/m^4 := by ring
    have he2 : (n : ℝ)*(v/m)*(D/m^3) = ((n : ℝ)*v*D)/m^4 := by ring
    rw [he1, he2]
    exact div_le_div_of_nonneg_right hterm (by positivity)
  have e2 : M2/m^2=2*(1-v/m)+a/m^2+B/m^2 := by
    rw [eh, he2]
    field_simp
  have e3 : M3/m^3=3*(1-v/m)*(M2/m^2)+3*(a/m^2)+R/m^3+D/m^3 := by
    rw [eh, he3]
    field_simp
  have hc := normalized_bound n hn (v/m) (a/m^2) (B/m^2) (R/m^3) (D/m^3)
    (M2/m^2) (M3/m^3) (by positivity) hv1 (by positivity)
    (by positivity) hb hr hd e2 e3
  have he1 : (n+2)*(M2/m^2)^2 = ((n+2)*M2^2)/m^4 := by ring
  have he2 : (n+1)*(M3/m^3) = ((n+1)*m*M3)/m^4 := by field_simp
  rw [he1, he2] at hc
  exact (div_le_div_iff_of_pos_right (by positivity : 0 < m^4)).mp hc

/-- The three compact renewal identities used in the paper agree with the existing
geometric-sum moment formulas. -/
theorem compact_renewal (x u v p q A B C D : ℝ) (hq : q ≠ 0) (hpq : p+q=1) :
    SSP.K2AllStages.renewalM1 x u v p q = (x+p*u)/q+v ∧
    SSP.K2AllStages.renewalM2 x u v p q A B =
      2*((x+p*u)/q)*SSP.K2AllStages.renewalM1 x u v p q+p*A/q+B ∧
    SSP.K2AllStages.renewalM3 x u v p q A B C D =
      3*((x+p*u)/q)*SSP.K2AllStages.renewalM2 x u v p q A B+
        3*(p*A/q)*SSP.K2AllStages.renewalM1 x u v p q+p*C/q+D := by
  have hp : p=1-q := by linarith
  rw [hp]
  unfold SSP.K2AllStages.renewalM1 SSP.K2AllStages.renewalM2 SSP.K2AllStages.renewalM3
    SSP.K2AllStages.renewalX1 SSP.K2AllStages.renewalX2 SSP.K2AllStages.renewalX3
    SSP.K2AllStages.kernelM1 SSP.K2AllStages.kernelM2 SSP.K2AllStages.kernelM3
  constructor
  · field_simp; ring
  constructor <;> field_simp <;> ring

/-- The improved renewal lemma for every `n≥2`. No return second-moment lower
bound and no positivity of the return mean are required. -/
theorem renewal_bound (n : ℕ) (hn : 2 ≤ n) (x u v p q A B C D : ℝ)
    (hx : 0 < x) (hu : 0 ≤ u) (hv : 0 ≤ v) (hp : 0 ≤ p) (hq : 0 < q)
    (hpq : p+q=1) (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hB : (n : ℝ)/(n-1)*v^2 ≤ B)
    (hret : (n+1)*A^2 ≤ (n : ℝ)*u*C)
    (hterm : (n+1)*B^2 ≤ (n : ℝ)*v*D) :
    SSP.K2AllStages.StageBound n
      (SSP.K2AllStages.renewalM1 x u v p q)
      (SSP.K2AllStages.renewalM2 x u v p q A B)
      (SSP.K2AllStages.renewalM3 x u v p q A B C D) := by
  let h := (x+p*u)/q
  let z := p/q
  have hh : 0 < h := by dsimp [h]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hR : 0 ≤ z*C := mul_nonneg hz hC
  have hret1 : (n+1)*(z*A)^2 ≤ (n : ℝ)*(z*u)*(z*C) := by
    have ht := mul_le_mul_of_nonneg_left hret (sq_nonneg z)
    nlinarith only [ht]
  have hzu : z*u ≤ h := by
    have he : h=z*u+x/q := by dsimp [h,z]; ring
    rw [he]
    have : 0 ≤ x/q := by positivity
    linarith
  have hret2 : (n+1)*(z*A)^2 ≤ (n : ℝ)*h*(z*C) := by
    have ht := mul_le_mul_of_nonneg_right hzu (mul_nonneg hn0 hR)
    nlinarith only [ht, hret1]
  obtain ⟨e1, e2, e3⟩ := compact_renewal x u v p q A B C D (ne_of_gt hq) hpq
  have hm : 0 < SSP.K2AllStages.renewalM1 x u v p q := by rw [e1]; exact add_pos_of_pos_of_nonneg hh hv
  have he1 : SSP.K2AllStages.renewalM1 x u v p q=h+v := e1
  have he2 : SSP.K2AllStages.renewalM2 x u v p q A B =
      2*h*SSP.K2AllStages.renewalM1 x u v p q+z*A+B := by
    dsimp [h,z]
    rw [e2]
    ring
  have he3 : SSP.K2AllStages.renewalM3 x u v p q A B C D =
      3*h*SSP.K2AllStages.renewalM2 x u v p q A B+
        3*(z*A)*SSP.K2AllStages.renewalM1 x u v p q+z*C+D := by
    dsimp [h,z]
    rw [e3]
    ring
  exact homogeneous_bound n hn _ h v (z*A) B (z*C) D _ _ hm hh hv
    (mul_nonneg hz hA) hD he1 hB hret2 hterm he2 he3

end SSP.K2Short
