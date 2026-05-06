import LeanC2.Numerical.GlobalBoundInput
import LeanC2.Numerical.Constants

set_option linter.style.whitespace false
set_option linter.style.longLine false

namespace LeanC2

def edgeCertificateJsonPath : String := "/home/thlinux/C2_Hipotese_De_Riemann/artefacts/json/edge_certificate.json"

def edgeCertificateJsonSha256 : String := "bf12fbb4769ff9638a3830472dc61011f5702003673f1257c717a185ed8a175c"

def edgeCertificateCommand : String := "python3 /home/thlinux/C2_Hipotese_De_Riemann/scripts/cert_regional_offaxis.py --kind edge --output /home/thlinux/C2_Hipotese_De_Riemann/artefacts/json/edge_certificate.json --primary-doc /home/thlinux/C2_Hipotese_De_Riemann/docs/c2_bulk_offaxis_edge_lemma.md --supporting-doc /home/thlinux/C2_Hipotese_De_Riemann/docs/c2_bulk_offaxis_glue.md --primary-script /home/thlinux/C2_Hipotese_De_Riemann/scripts/colagem_global.py --default-t0 100 --default-eps-num 1 --default-eps-den 20 --emit-lean --lean-output /home/thlinux/C2_Hipotese_De_Riemann/Lean/LeanC2/Numerical/Generated/EdgeCertificate.lean"

def edgeCertificatePrimaryDoc : String := "/home/thlinux/C2_Hipotese_De_Riemann/docs/c2_bulk_offaxis_edge_lemma.md"

def edgeCertificatePrimaryDocSha256 : String := "276046ffe1ef3fc1f7e187292a7d701e8a3d1e9f23f674d2c4dd6d99414a0a68"

def edgeCertificateSupportingDoc : String := "/home/thlinux/C2_Hipotese_De_Riemann/docs/c2_bulk_offaxis_glue.md"

def edgeCertificateSupportingDocSha256 : String := "1b26bb9aa6c2b415ee94f9dca33ce79ccd7441a10c4a25fc2944419601b6ec45"

def edgeCertificatePrimaryScript : String := "/home/thlinux/C2_Hipotese_De_Riemann/scripts/colagem_global.py"

def edgeCertificatePrimaryScriptSha256 : String := "47f99c66c4dcc54a318400ebd3ecc2b8fc22bf2de96dde7c316552d8542816eb"

def edgeCertificateDefaultT0 : Real := 100

noncomputable def edgeCertificateDefaultEps : Real := 1 / 20

theorem edgeCertificate_defaultT0_eq : defaultT0 = 100 := by
  rfl

theorem edgeCertificate_defaultEps_eq : defaultEps = 1 / 20 := by
  rfl

/--
External edge-region certificate packaged by `scripts/cert_regional_offaxis.py`.

Audit trail:
- json artifact: `edgeCertificateJsonPath`
- sha256: `edgeCertificateJsonSha256`
- packaging command: `edgeCertificateCommand`
- primary doc: `edgeCertificatePrimaryDoc`
- supporting doc: `edgeCertificateSupportingDoc`
- primary script: `edgeCertificatePrimaryScript`
- default threshold: `t >= 100`, `eps = 1/20`

This certificate supplies one regional leg of the canonical high off-strip package.
-/
axiom certifiedCanonicalEdgeGlobalBoundCertificate :
  CanonicalEdgeGlobalBoundCertificate

end LeanC2
