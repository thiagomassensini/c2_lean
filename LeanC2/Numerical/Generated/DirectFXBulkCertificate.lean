import LeanC2.Numerical.GlobalBoundInput
import LeanC2.Numerical.Constants
import LeanC2.Bulk.DirectFX

set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace LeanC2

def directFXBulkCertificateJsonPath : String := "/home/thlinux/C2_Hipotese_De_Riemann/artefacts/json/directfx_right_bulk_certificate.json"

def directFXBulkCertificateJsonSha256 : String := "dbb7c40a3640c10af40a8c04ab8c10ce83a15b24ff6c5a3ce9fbf8b2ec54b9ae"

def directFXBulkCertificateCommand : String := "python3 /home/thlinux/C2_Hipotese_De_Riemann/scripts/cert_directfx_bulk.py --output /home/thlinux/C2_Hipotese_De_Riemann/artefacts/json/directfx_right_bulk_certificate.json --certificate-form right-residual --default-t0 100 --default-eps-num 1 --default-eps-den 20 --quartet-doc /home/thlinux/C2_Hipotese_De_Riemann/docs/c2_quarteto_dominante_cutoff.md --cutoff-decay-doc /home/thlinux/C2_Hipotese_De_Riemann/docs/c2_prova_taxa_decaimento_cutoff.md --adaptive-cutoff-doc /home/thlinux/C2_Hipotese_De_Riemann/docs/c2_cutoff_adaptativo_quarteto.md --directfx-lean /home/thlinux/C2_Hipotese_De_Riemann/Lean/LeanC2/Bulk/DirectFX.lean --dominant-quartet-lean /home/thlinux/C2_Hipotese_De_Riemann/Lean/LeanC2/Cutoff/DominantQuartet.lean --residue-lean /home/thlinux/C2_Hipotese_De_Riemann/Lean/LeanC2/Cutoff/Residue.lean --bulk-scan-script /home/thlinux/C2_Hipotese_De_Riemann/scripts/c2_bulk_offaxis_certificate.py --rouche-script /home/thlinux/C2_Hipotese_De_Riemann/scripts/c2_rouche_rectangle.py --emit-lean --lean-output /home/thlinux/C2_Hipotese_De_Riemann/Lean/LeanC2/Numerical/Generated/DirectFXBulkCertificate.lean --verify-grid --verify-kind residual --verify-side right --verify-x 500 --verify-t-samples 15 --verify-sigma-samples 6 --verify-t-lo 100.0 --verify-t-hi 1000.0 --require-verified"

def directFXBulkCertificateQuartetDoc : String := "/home/thlinux/C2_Hipotese_De_Riemann/docs/c2_quarteto_dominante_cutoff.md"

def directFXBulkCertificateQuartetDocSha256 : String := "a908d90fe291b56f4819eab7a5d0510a353376b2b717ef0733ead634cf6b6f5a"

def directFXBulkCertificateCutoffDecayDoc : String := "/home/thlinux/C2_Hipotese_De_Riemann/docs/c2_prova_taxa_decaimento_cutoff.md"

def directFXBulkCertificateCutoffDecayDocSha256 : String := "a00b202ecc22fd312d2ff4e9f78fdb941866f7dd49c76031a2c6f327d08a374d"

def directFXBulkCertificateAdaptiveCutoffDoc : String := "/home/thlinux/C2_Hipotese_De_Riemann/docs/c2_cutoff_adaptativo_quarteto.md"

def directFXBulkCertificateAdaptiveCutoffDocSha256 : String := "b7d30dfaafd6a74a7aa469480798ae400f933199f4a9a20fc60acbc73576b5b7"

def directFXBulkCertificateDirectfxLean : String := "/home/thlinux/C2_Hipotese_De_Riemann/Lean/LeanC2/Bulk/DirectFX.lean"

def directFXBulkCertificateDirectfxLeanSha256 : String := "237644e8bb3cbb923be84a97663960f371d8227990ed261e2767e241e39db923"

def directFXBulkCertificateDominantQuartetLean : String := "/home/thlinux/C2_Hipotese_De_Riemann/Lean/LeanC2/Cutoff/DominantQuartet.lean"

def directFXBulkCertificateDominantQuartetLeanSha256 : String := "bb58ac84845a3a7db6c6066ff68a35db0b1d938fedb87342e89e0e481b666311"

def directFXBulkCertificateResidueLean : String := "/home/thlinux/C2_Hipotese_De_Riemann/Lean/LeanC2/Cutoff/Residue.lean"

def directFXBulkCertificateResidueLeanSha256 : String := "dfac98bfa028a0eb73be4175a6ec8981af8d758432f12e8b7ed838a98620f429"

def directFXBulkCertificateBulkScanScript : String := "/home/thlinux/C2_Hipotese_De_Riemann/scripts/c2_bulk_offaxis_certificate.py"

def directFXBulkCertificateBulkScanScriptSha256 : String := "dee787eeb6e92fe9d4635362044e75a1c428c16d7ffef3761b70d9ecd04a2dd9"

def directFXBulkCertificateRoucheScript : String := "/home/thlinux/C2_Hipotese_De_Riemann/scripts/c2_rouche_rectangle.py"

def directFXBulkCertificateRoucheScriptSha256 : String := "b8c1259a99bb139aaefde575f23b007fde457395af957a8418005164d3fc4ec7"

def directFXBulkCertificateDefaultT0 : Real := 100

noncomputable def directFXBulkCertificateDefaultEps : Real := 1 / 20

theorem directFXBulkCertificate_defaultT0_eq : defaultT0 = 100 := by
  rfl

theorem directFXBulkCertificate_defaultEps_eq : defaultEps = 1 / 20 := by
  rfl

/-
External direct-FX certificate packaged by `scripts/cert_directfx_bulk.py`.

Audit trail:
- json artifact: `directFXBulkCertificateJsonPath`
- sha256: `directFXBulkCertificateJsonSha256`
- packaging command: `directFXBulkCertificateCommand`
- quartet doc: `directFXBulkCertificateQuartetDoc`
- cutoff decay doc: `directFXBulkCertificateCutoffDecayDoc`
- adaptive cutoff doc: `directFXBulkCertificateAdaptiveCutoffDoc`
- DirectFX Lean interface: `directFXBulkCertificateDirectfxLean`
- DominantQuartet Lean source: `directFXBulkCertificateDominantQuartetLean`
- Residue Lean source: `directFXBulkCertificateResidueLean`

Logical route:
- Lean proves the quartet/tail margin for `sharpCutoffFamily`.
- Lean proves `canonicalCutoffFamily = sharpCutoffFamily + canonicalCutoffResidual`.
- certificate statement: `DirectFXCanonicalRightBulkCertificate`.
- region: `rightBulkRegion`.
- direct inequality: `||canonicalCutoffResidual X s|| < dominantQuartetBulkMarginCoeff s * ||cutoffFirstShell X s||`.
- A valid external certificate must supply the strict dominance on its stated region.
- default threshold: `t >= 100`, `eps = 1/20`
-/
/--
Candidate direct-FX certificate.

No axiom is emitted by default. Use `scripts/cert_directfx_bulk.py --trust-external`
only after the strict direct dominance has been independently validated.
-/
def directFXBulkCertificateCandidateStatement : String :=
  "DirectFXCanonicalRightBulkCertificate"

end LeanC2
