import LeanC2.Numerical.GlobalBoundInput
import LeanC2.Numerical.Constants

set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace LeanC2

def finiteHeightCertificateJsonPath : String := "/home/thlinux/C2_Hipotese_De_Riemann/artefacts/json/finite_height_certificate.json"

def finiteHeightCertificateJsonSha256 : String := "06749a63027e667cb5bcf900e5b4bedd9c1f4e6719b4875b62f5de352c1a8a8a"

def finiteHeightCertificateCommand : String := "python3 /home/thlinux/C2_Hipotese_De_Riemann/scripts/cert_finite_height.py --output /home/thlinux/C2_Hipotese_De_Riemann/artefacts/json/finite_height_certificate.json --certified-height 448 --default-t0 100 --zeros-covered 150 --primary-doc /home/thlinux/C2_Hipotese_De_Riemann/docs/teorema_faixa_diadica_zero_free.md --supporting-doc /home/thlinux/C2_Hipotese_De_Riemann/docs/c2_bulk_offaxis_glue.md --primary-script /home/thlinux/C2_Hipotese_De_Riemann/scripts/colagem_global.py --supporting-script /home/thlinux/C2_Hipotese_De_Riemann/scripts/teorema_faixa_diadica.py --emit-lean --lean-output /home/thlinux/C2_Hipotese_De_Riemann/Lean/LeanC2/Numerical/Generated/FiniteHeightCertificate.lean"

def finiteHeightCertificatePrimaryDoc : String := "/home/thlinux/C2_Hipotese_De_Riemann/docs/teorema_faixa_diadica_zero_free.md"

def finiteHeightCertificatePrimaryDocSha256 : String := "007afcde29a43ac3897b5d971dfaa48a58a423e41b30d996f6c23ec252202b3a"

def finiteHeightCertificateSupportingDoc : String := "/home/thlinux/C2_Hipotese_De_Riemann/docs/c2_bulk_offaxis_glue.md"

def finiteHeightCertificateSupportingDocSha256 : String := "1b26bb9aa6c2b415ee94f9dca33ce79ccd7441a10c4a25fc2944419601b6ec45"

def finiteHeightCertificatePrimaryScript : String := "/home/thlinux/C2_Hipotese_De_Riemann/scripts/colagem_global.py"

def finiteHeightCertificatePrimaryScriptSha256 : String := "47f99c66c4dcc54a318400ebd3ecc2b8fc22bf2de96dde7c316552d8542816eb"

def finiteHeightCertificateSupportingScript : String := "/home/thlinux/C2_Hipotese_De_Riemann/scripts/teorema_faixa_diadica.py"

def finiteHeightCertificateSupportingScriptSha256 : String := "e2a8a802cb5d8a6bf16af7e4050f03679c9a7d7d5d8b751d1b66c7137865ad0f"

def finiteHeightCertificateCertifiedHeight : Real := 448

def finiteHeightCertificateDefaultT0 : Real := 100

def finiteHeightCertificateZerosCovered : Nat := 150

theorem finiteHeightCertificate_defaultCertifiedHeight_eq :
    defaultCertifiedHeight = 448 := by
  rfl

theorem finiteHeightCertificate_defaultT0_eq : defaultT0 = 100 := by
  rfl

/--
External finite-height certificate packaged by `scripts/cert_finite_height.py`.

Audit trail:
- json artifact: `finiteHeightCertificateJsonPath`
- sha256: `finiteHeightCertificateJsonSha256`
- packaging command: `finiteHeightCertificateCommand`
- primary doc: `finiteHeightCertificatePrimaryDoc`
- supporting doc: `finiteHeightCertificateSupportingDoc`
- primary script: `finiteHeightCertificatePrimaryScript`
- supporting script: `finiteHeightCertificateSupportingScript`
- certified height: `t <= 448`
- zeros covered in the documented run: `150`

This certificate supplies the finite-height leg of the canonical default global-bound package.
-/
axiom certifiedCanonicalFiniteHeightGlobalBoundCertificate :
  CanonicalFiniteHeightGlobalBoundCertificate

end LeanC2
