import LeanC2.Numerical.GlobalBoundInput
import LeanC2.Numerical.Constants
import LeanC2.Bulk.Route3

set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace LeanC2

def bulkCertificateJsonPath : String := "/home/thlinux/C2_Hipotese_De_Riemann/artefacts/json/bulk_certificate.json"

def bulkCertificateJsonSha256 : String := "6a0a2ae24f4b6846497c3dba853d06df2b5ac5784f72be5c1a63271763b8f104"

def bulkCertificateCommand : String := "python3 /home/thlinux/C2_Hipotese_De_Riemann/scripts/cert_regional_offaxis.py --kind bulk --output /home/thlinux/C2_Hipotese_De_Riemann/artefacts/json/bulk_certificate.json --primary-doc /home/thlinux/C2_Hipotese_De_Riemann/docs/c2_bulk_offaxis_route3_tilt.md --supporting-doc /home/thlinux/C2_Hipotese_De_Riemann/docs/c2_bulk_offaxis_glue.md --primary-script /home/thlinux/C2_Hipotese_De_Riemann/scripts/c2_bulk_offaxis_certificate.py --default-t0 100 --default-eps-num 1 --default-eps-den 20 --supporting-script /home/thlinux/C2_Hipotese_De_Riemann/scripts/c2_rouche_rectangle.py --emit-lean --lean-output /home/thlinux/C2_Hipotese_De_Riemann/Lean/LeanC2/Numerical/Generated/BulkCertificate.lean"

def bulkCertificatePrimaryDoc : String := "/home/thlinux/C2_Hipotese_De_Riemann/docs/c2_bulk_offaxis_route3_tilt.md"

def bulkCertificatePrimaryDocSha256 : String := "483bd8c3078ed3bf4f4fa174582b23f62c71f3021044762e0816e54303743dee"

def bulkCertificateSupportingDoc : String := "/home/thlinux/C2_Hipotese_De_Riemann/docs/c2_bulk_offaxis_glue.md"

def bulkCertificateSupportingDocSha256 : String := "1b26bb9aa6c2b415ee94f9dca33ce79ccd7441a10c4a25fc2944419601b6ec45"

def bulkCertificatePrimaryScript : String := "/home/thlinux/C2_Hipotese_De_Riemann/scripts/c2_bulk_offaxis_certificate.py"

def bulkCertificatePrimaryScriptSha256 : String := "dee787eeb6e92fe9d4635362044e75a1c428c16d7ffef3761b70d9ecd04a2dd9"

def bulkCertificateSupportingScript : String := "/home/thlinux/C2_Hipotese_De_Riemann/scripts/c2_rouche_rectangle.py"

def bulkCertificateSupportingScriptSha256 : String := "b8c1259a99bb139aaefde575f23b007fde457395af957a8418005164d3fc4ec7"

def bulkCertificateDefaultT0 : Real := 100

noncomputable def bulkCertificateDefaultEps : Real := 1 / 20

theorem bulkCertificate_defaultT0_eq : defaultT0 = 100 := by
  rfl

theorem bulkCertificate_defaultEps_eq : defaultEps = 1 / 20 := by
  rfl

/--
External bulk-region certificate packaged by `scripts/cert_regional_offaxis.py`.

Audit trail:
- json artifact: `bulkCertificateJsonPath`
- sha256: `bulkCertificateJsonSha256`
- packaging command: `bulkCertificateCommand`
- primary doc: `bulkCertificatePrimaryDoc`
- supporting doc: `bulkCertificateSupportingDoc`
- primary script: `bulkCertificatePrimaryScript`
- supporting script: `bulkCertificateSupportingScript`
- delta model: `deltaStarLowerModel`

Logical route:
- Route 3 (`docs/c2_bulk_offaxis_route3_tilt.md`) is the primary analytic bulk route.
- Route 1 numerical scans and Route 2 Rouche checks are support/audit material, not Lean kernel dependencies.
- default threshold: `t >= 100`, `eps = 1/20`

This certificate supplies the Route 3 analytic inputs for one regional leg of the canonical
high off-strip package. The final bulk nonvanishing proposition is derived below from
`canonicalBulkGlobalBoundCertificate_of_route3`.
-/
axiom certifiedCanonicalRoute3BulkCertificate :
  Route3CanonicalBulkCertificate

theorem certifiedCanonicalBulkGlobalBoundCertificate :
  CanonicalBulkGlobalBoundCertificate := by
  exact canonicalBulkGlobalBoundCertificate_of_route3
    certifiedCanonicalRoute3BulkCertificate

end LeanC2
