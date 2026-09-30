import VCVio.OracleComp.QueryTracking.Structures

/-!
# Porting compatibility

Newer VCVio makes `OracleSpec.QueryCache` reducible, so `c₁ ≤ c₂` on a cache whose range carries
an order (e.g. `BitVec`) would elaborate to the pointwise `Pi.hasLe` order instead of the cache
extension order. This high-priority instance restores the original meaning of `≤` on caches.
-/

namespace OracleSpec.QueryCache

instance (priority := high) instLEExtension {ι : Type*} {spec : OracleSpec ι} :
    LE (QueryCache spec) :=
  @Preorder.toLE _ (@PartialOrder.toPreorder _ QueryCache.instPartialOrder)

end OracleSpec.QueryCache
