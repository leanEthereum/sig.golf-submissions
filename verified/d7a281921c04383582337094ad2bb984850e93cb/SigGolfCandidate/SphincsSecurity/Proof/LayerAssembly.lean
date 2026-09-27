import SigGolfCandidate.SphincsSecurity.Proof.SignatureLayout
open OracleComp OracleSpec
namespace SphincsSecurity
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit true
set_option maxRecDepth 4096

def restrictPath (lay : Layer) (path : Fin maxLayerHeight → α) : Fin (layerHeight lay) → α :=
  fun level => path (level.castLE (layerHeight_le lay))

end SphincsSecurity
