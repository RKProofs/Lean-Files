import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! Small cubic closure identities keep coefficient proofs from expanding the
polynomials hidden in their parameters. All identities are kernel checked. -/
set_option autoImplicit false
namespace SSP.CubicBernstein

/-- A real function represented by a polynomial of degree at most three. -/
def IsCubic (f : ℝ → ℝ) : Prop :=
  ∃ a b c d : ℝ, f = fun t => a+b*t+c*t^2+d*t^3

theorem IsCubic.add {f g : ℝ → ℝ} (hf : IsCubic f) (hg : IsCubic g) :
    IsCubic (fun t => f t+g t) := by
  obtain ⟨a,b,c,d,rfl⟩ := hf
  obtain ⟨e,f,g,h,rfl⟩ := hg
  refine ⟨a+e,b+f,c+g,d+h,?_⟩
  funext t; ring

theorem IsCubic.const_mul {f : ℝ → ℝ} (hf : IsCubic f) (k : ℝ) :
    IsCubic (fun t => k*f t) := by
  obtain ⟨a,b,c,d,rfl⟩ := hf
  refine ⟨k*a,k*b,k*c,k*d,?_⟩
  funext t; ring

theorem IsCubic.comp_affine {f : ℝ → ℝ} (hf : IsCubic f) (u v : ℝ) :
    IsCubic (fun t => f (u+v*t)) := by
  obtain ⟨a,b,c,d,rfl⟩ := hf
  refine ⟨a+b*u+c*u^2+d*u^3,v*(b+2*c*u+3*d*u^2),v^2*(c+3*d*u),v^3*d,?_⟩
  funext t; ring

theorem homogeneous_affine (a b c d k l : ℝ) :
    IsCubic (fun t => a*t^3+b*t^2*(k+l*t)+c*t*(k+l*t)^2+d*(k+l*t)^3) := by
  refine ⟨d*k^3,c*k^2+3*d*k^2*l,b*k+2*c*k*l+3*d*k*l^2,
    a+b*l+c*l^2+d*l^3,?_⟩
  funext t; ring

theorem IsCubic.interpolate {f : ℝ → ℝ} (hf : IsCubic f) (t : ℝ) :
    f t = f 0*(1-t)^3+
      3*(-(5/6)*f 0+(1/3)*f 1+3*f (1/3)-(3/2)*f (2/3))*t*(1-t)^2+
      3*((1/3)*f 0-(5/6)*f 1-(3/2)*f (1/3)+3*f (2/3))*t^2*(1-t)+f 1*t^3 := by
  obtain ⟨a,b,c,d,rfl⟩ := hf
  ring

end SSP.CubicBernstein
