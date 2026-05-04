import Mathlib

namespace LeanC2

noncomputable def constA : Real := 7931 / 5000
noncomputable def constC : Real := 169 / 1000
noncomputable def constK1 : Real := 2877 / 50
noncomputable def constK2 : Real := 381 / 5
noncomputable def constCT : Real := 531 / 4

def defaultX : Nat := 8850
def defaultT0 : Real := 100

/-!
Numeric constants fixed by the current C2 proof chain.

Primary sources:
- docs/c2_certificacao_bound_global.md
- docs/c2_cutoff_adaptativo_quarteto.md
-/

end LeanC2
