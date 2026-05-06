import Mathlib

namespace LeanC2

noncomputable def constA : Real := 7931 / 5000
noncomputable def constC : Real := 17 / 100
noncomputable def constK1 : Real := 2877 / 50
noncomputable def constK2 : Real := 381 / 5
noncomputable def constCT : Real := 531 / 4
noncomputable def defaultEps : Real := 1 / 20

def defaultX : Nat := 8850
def defaultT0 : Real := 100
def defaultCertifiedHeight : Real := 448

theorem defaultEps_pos : 0 < defaultEps := by
  norm_num [defaultEps]

theorem defaultEps_nonneg : 0 ≤ defaultEps := by
  exact le_of_lt defaultEps_pos

theorem constA_pos : 0 < constA := by
  norm_num [constA]

theorem constA_nonneg : 0 ≤ constA := by
  exact le_of_lt constA_pos

theorem constC_pos : 0 < constC := by
  norm_num [constC]

theorem constC_nonneg : 0 ≤ constC := by
  exact le_of_lt constC_pos

theorem defaultT0_le_defaultCertifiedHeight : defaultT0 ≤ defaultCertifiedHeight := by
  norm_num [defaultT0, defaultCertifiedHeight]

/-!
Numeric constants fixed by the current C2 proof chain.

Primary sources:
- docs/c2_certificacao_bound_global.md
- docs/c2_cutoff_adaptativo_quarteto.md
-/

end LeanC2
