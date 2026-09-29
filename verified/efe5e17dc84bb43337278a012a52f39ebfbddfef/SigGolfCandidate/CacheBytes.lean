import SigGolfCandidate.Legacy

/-!
# The cache size

The contract lets a submission choose its cache size `K` (`Sizes.cache ≤ MAX_CACHE_BYTES`). This
submission keeps `K = 2^17 = MAX_CACHE_BYTES`, the size the contract fixed before `K` became
submission-chosen (the cache content uses its first 65 536 bytes; the rest is zero).
-/

namespace SigGolfCandidate

/-- The cache size `K` this submission declares (`claim.json`, `SigGolfCandidate.Legacy.Challenge.cache_bytes`). -/
def CACHE_BYTES : Nat := 2 ^ 17

/-- The cache bytes key generation publishes and signing reads. -/
abbrev Cache := SigGolfCandidate.Legacy.Bytes CACHE_BYTES

end SigGolfCandidate
