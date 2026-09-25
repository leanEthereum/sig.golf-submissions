import SigGolfCandidate.Hypertree.SecurityMonitorIndexContactUpdates
import SigGolfCandidate.Hypertree.SecurityGraphOracle

namespace SigGolfCandidate.Hypertree.SecurityMonitorIndexContact
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle SecurityIndexQuery
  SecurityMonitorIndexState SecurityIndexTrace SecurityMonitorIndexInvariant
  SecurityGraphFactor SecurityGraphOracle
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Index bookkeeping invariants, including input-labelled fresh-draw provenance. -/
def Tracked (nonces : NonceTable) (cache : QueryCache HashSpec) (history : History) : Prop :=
  NonceCovered cache history ∧ SignedCached nonces cache history ∧
    ∃ draws, Provenance nonces cache history draws

theorem tracked_empty (nonces : NonceTable) : Tracked nonces ∅ {} :=
  ⟨nonceCovered_empty, signedCached_empty nonces, [], provenance_empty nonces⟩

theorem Tracked.keygen {nonces : NonceTable} {cache : QueryCache HashSpec} {history : History}
    (tracked : Tracked nonces cache history) : Tracked nonces cache (recordKeygen history) := by
  obtain ⟨covered, cached, draws, provenance⟩ := tracked
  exact ⟨covered, cached.recordKeygen, draws, provenance.keygen⟩

attribute [local irreducible] recordParsed indexInput

theorem Provenance.public_skip {nonces : NonceTable}
    {cache : QueryCache HashSpec} {history : History} {draws : List Draw}
    (p : Provenance nonces cache history draws) (query : Query) (hit : Bool) (answer : BitVec 256)
    (parsed : parse query = none) :
    Provenance nonces cache (recordPublic history query hit answer) draws := by
  constructor
  · change _ = (recordParsed history query (parse query) (decide _) hit answer).indexTrace
    rw [parsed, parsed_trace_none]
    exact p.trace
  · exact p.cached
  · intro message member
    rw [public_messages] at member
    rcases p.signed message member with guessed | marked
    · exact Or.inl (guessed.public query hit answer)
    · exact Or.inr marked

theorem Tracked.public_skip {nonces : NonceTable}
    {cache : QueryCache HashSpec} {history : History}
    (tracked : Tracked nonces cache history) (query : Query) (hit : Bool) (answer : BitVec 256)
    (parsed : parse query = none) :
    Tracked nonces cache (recordPublic history query hit answer) := by
  obtain ⟨covered, cached, draws, provenance⟩ := tracked
  exact ⟨covered.public_preserved query hit answer, cached.recordPublic query hit answer,
    draws, provenance.public_skip query hit answer parsed⟩

theorem Tracked.public_random {nonces : NonceTable}
    {cache : QueryCache HashSpec} {history : History}
    (tracked : Tracked nonces cache history) (query : Query) (answer : BitVec 256)
    (residual : QueryCache HashSpec)
    (member : (answer, residual) ∈ support ((randomOracle (spec := HashSpec) query).run cache)) :
    Tracked nonces residual (recordPublic history query (cache query).isSome answer) := by
  obtain ⟨covered, cached, draws, provenance⟩ := tracked
  cases present : cache query with
  | some value =>
    simp only [randomOracle.run_eq, present, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩
    exact ⟨covered.public_preserved query true answer, cached.recordPublic query true answer,
      draws, provenance.public_hit query answer⟩
  | none =>
    simp only [randomOracle.run_eq, present, bind_pure_comp, support_map, Set.mem_image] at member
    obtain ⟨value, _, equal⟩ := member
    cases equal
    refine ⟨covered.public_fill query false answer, cached.public_fill query false answer, ?_⟩
    cases parsed : parse query with
    | none => exact ⟨draws, provenance.public_other query answer parsed⟩
    | some pair =>
      rcases pair with ⟨message, nonce⟩
      exact ⟨_, provenance.public_fresh query answer present message nonce parsed⟩

theorem canonical_parse_none (privateAnswers : SecurityDerivation.Slot → BitVec 256)
    (labels : SecurityGraph.Labels) (query : Query) (answer : BitVec 256)
    (known : canonical privateAnswers labels query = some answer) : parse query = none := by
  apply (parse_none_iff query).mpr
  intro message nonce same
  have outside : SecurityGraphQuery.locate query = none := same ▸ locate_index message nonce
  simp only [canonical, outside] at known
  cases known

theorem Tracked.public_oracle {nonces : NonceTable}
    {cache : QueryCache HashSpec} {history : History}
    (tracked : Tracked nonces cache history) (privateAnswers : SecurityDerivation.Slot → BitVec 256)
    (labels : SecurityGraph.Labels) (query : Query) (answer : BitVec 256) (residual : QueryCache HashSpec)
    (member : (answer,residual) ∈ support ((publicOracle privateAnswers labels query).run cache)) :
    Tracked nonces residual (recordPublic history query (cache query).isSome answer) := by
  cases known : canonical privateAnswers labels query with
  | none =>
    simp only [publicOracle, known] at member
    exact tracked.public_random query answer residual member
  | some value =>
    simp only [publicOracle, known, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩
    exact tracked.public_skip query (residual query).isSome answer (canonical_parse_none _ _ query answer known)

theorem Tracked.sign_random {nonces : NonceTable}
    {cache : QueryCache HashSpec} {history : History}
    (tracked : Tracked nonces cache history) (message : Message) (answer : BitVec 256)
    (residual : QueryCache HashSpec)
    (member : (answer, residual) ∈ support
      ((randomOracle (spec := HashSpec) (indexInput message (nonces message))).run cache)) :
    Tracked nonces residual
      (recordSign history message (cache (indexInput message (nonces message))).isSome answer) := by
  obtain ⟨covered, cached, draws, provenance⟩ := tracked
  cases present : cache (indexInput message (nonces message)) with
  | some value =>
    simp only [randomOracle.run_eq, present, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩
    exact ⟨covered.sign_preserved message true answer,
      cached.recordSign message true answer (by rw [present]; exact Option.some_ne_none _),
      draws, provenance.sign_hit covered message answer present⟩
  | none =>
    simp only [randomOracle.run_eq, present, bind_pure_comp, support_map, Set.mem_image] at member
    obtain ⟨value, _, equal⟩ := member
    cases equal
    exact ⟨covered.sign_fill message (nonces message) false answer,
      cached.sign_fill message (nonces message) rfl false answer,
      _, provenance.sign_fresh message answer present (cached.miss_is_first message present)⟩

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorIndexContact.Tracked.public_oracle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Tracked.public_oracle
end SigGolfCandidate.Hypertree.SecurityMonitorIndexContact
