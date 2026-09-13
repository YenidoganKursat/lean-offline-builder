import Mathlib

namespace ScienceLean

noncomputable section

namespace Chemistry

def equilibriumConstant (ΔG R T : ℝ) : ℝ := Real.exp (-ΔG / (R * T))

theorem equilibriumConstant_pos (ΔG R T : ℝ) :
    0 < equilibriumConstant ΔG R T := by
  exact Real.exp_pos _

end Chemistry

namespace PhotoPhysics

def quantumYield (kr knr : ℝ) : ℝ := kr / (kr + knr)

theorem quantumYield_nonneg (kr knr : ℝ) (hkr : 0 ≤ kr)
    (hden : 0 < kr + knr) : 0 ≤ quantumYield kr knr := by
  unfold quantumYield
  positivity

theorem quantumYield_le_one (kr knr : ℝ) (hknr : 0 ≤ knr)
    (hden : 0 < kr + knr) : quantumYield kr knr ≤ 1 := by
  unfold quantumYield
  rw [div_le_iff₀ hden]
  linarith

end PhotoPhysics
namespace Biology

def michaelisMenten (vmax km s : ℝ) : ℝ := vmax * s / (km + s)

theorem michaelisMenten_nonneg (vmax km s : ℝ)
    (hv : 0 ≤ vmax) (hs : 0 ≤ s) (hden : 0 < km + s) :
    0 ≤ michaelisMenten vmax km s := by
  unfold michaelisMenten
  positivity

end Biology

namespace Estimation

def scalarKalmanGain (P R : ℝ) : ℝ := P / (P + R)

theorem scalarKalmanGain_nonneg (P R : ℝ) (hP : 0 ≤ P)
    (hden : 0 < P + R) : 0 ≤ scalarKalmanGain P R := by
  unfold scalarKalmanGain
  positivity

theorem scalarKalmanGain_le_one (P R : ℝ) (hR : 0 ≤ R)
    (hden : 0 < P + R) : scalarKalmanGain P R ≤ 1 := by
  unfold scalarKalmanGain
  rw [div_le_iff₀ hden]
  linarith

end Estimation
namespace Materials

def arrhenius (A Ea R T : ℝ) : ℝ := A * Real.exp (-Ea / (R * T))

theorem arrhenius_nonneg (A Ea R T : ℝ) (hA : 0 ≤ A) :
    0 ≤ arrhenius A Ea R T := by
  unfold arrhenius
  positivity

end Materials

namespace Thermodynamics

def carnotEfficiency (Tc Th : ℝ) : ℝ := 1 - Tc / Th

theorem carnotEfficiency_nonneg (Tc Th : ℝ)
    (hTc : 0 ≤ Tc) (hTh : 0 < Th) (hle : Tc ≤ Th) :
    0 ≤ carnotEfficiency Tc Th := by
  unfold carnotEfficiency
  rw [sub_nonneg, div_le_one hTh]
  exact hle

theorem carnotEfficiency_le_one (Tc Th : ℝ)
    (hTc : 0 ≤ Tc) (hTh : 0 < Th) : carnotEfficiency Tc Th ≤ 1 := by
  unfold carnotEfficiency
  have hdiv : 0 ≤ Tc / Th := by positivity
  linarith

end Thermodynamics
namespace PDE

def quadraticEnergy (u v : ℝ) : ℝ := u^2 + v^2

theorem quadraticEnergy_nonneg (u v : ℝ) : 0 ≤ quadraticEnergy u v := by
  unfold quadraticEnergy
  positivity

end PDE

namespace Astrophysics

def escapeSpeedSquared (μ r : ℝ) : ℝ := 2 * μ / r

theorem escapeSpeedSquared_nonneg (μ r : ℝ)
    (hμ : 0 ≤ μ) (hr : 0 < r) : 0 ≤ escapeSpeedSquared μ r := by
  unfold escapeSpeedSquared
  positivity

end Astrophysics

namespace SignalProcessing

def weightedVariance (w x₁ x₂ : ℝ) : ℝ :=
  w * x₁^2 + (1 - w) * x₂^2

theorem weightedVariance_nonneg (w x₁ x₂ : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : 0 ≤ weightedVariance w x₁ x₂ := by
  unfold weightedVariance
  positivity

end SignalProcessing

end ScienceLean
