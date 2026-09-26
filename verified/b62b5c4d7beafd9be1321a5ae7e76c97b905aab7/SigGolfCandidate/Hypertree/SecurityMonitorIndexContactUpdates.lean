import SigGolfCandidate.Hypertree.SecurityMonitorIndexContact

namespace SigGolfCandidate.Hypertree.SecurityMonitorIndexContact
open SigGolf OracleComp OracleSpec Reference SecurityRandomOracle SecurityIndexQuery
  SecurityMonitorIndexState SecurityIndexTrace
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

 theorem NonceHit.public {nonces : Message → Bytes 32} {history : History}
    (hit : NonceHit nonces history) (query : Query) (cached : Bool) (answer : BitVec 256) :
    NonceHit nonces (recordPublic history query cached answer) := by
  obtain ⟨message, member⟩ := hit
  exact ⟨message, public_guesses_preserved history query cached answer _ member⟩

 theorem parsed_trace_hit (history : History) (query : Query) (parsed : Option (Message × Bytes 32))
    (secretKey : Bool) (answer : BitVec 256) :
    (recordParsed history query parsed secretKey true answer).indexTrace = history.indexTrace := by
  cases parsed with
  | none => cases secretKey <;> rfl
  | some pair => cases pair; rfl

 theorem parsed_trace_none (history : History) (query : Query) (secretKey cached : Bool) (answer : BitVec 256) :
    (recordParsed history query none secretKey cached answer).indexTrace = history.indexTrace := by
  cases secretKey <;> rfl

 theorem parsed_trace_fresh (history : History) (query : Query) (pair : Message × Bytes 32)
    (secretKey : Bool) (answer : BitVec 256) :
    (recordParsed history query (some pair) secretKey false answer).indexTrace =
      history.indexTrace ++ [(false, answer.extractLsb' 0 160)] := by cases pair; rfl

attribute [local irreducible] recordParsed indexInput

 theorem Provenance.public_hit {nonces : Message → Bytes 32}
    {cache : QueryCache HashSpec} {history : History} {draws : List Draw}
    (p : Provenance nonces cache history draws) (query : Query) (answer : BitVec 256) :
    Provenance nonces cache (recordPublic history query true answer) draws := by
  constructor
  · exact p.trace.trans (parsed_trace_hit history query (parse query) (decide _) answer).symm
  · exact p.cached
  · intro message member
    rw [public_messages] at member
    rcases p.signed message member with hit | marked
    · exact Or.inl (hit.public query true answer)
    · exact Or.inr marked

theorem cache_fill_preserves (cache : QueryCache HashSpec) (query : Query) (answer : BitVec 256)
    (miss : cache query = none) (other : Query) (value : BitVec 256)
    (present : cache other = some value) : (cache.cacheQuery query answer) other = some value := by
  by_cases same : other = query
  · rw [same, miss] at present
    cases present
  · rw [QueryCache.cacheQuery_of_ne _ _ same]
    exact present

theorem cached_fill {cache : QueryCache HashSpec} {draws : List Draw}
    (old : ∀ m r value, cache (indexInput m r) = some value →
      ∃ mark, (indexInput m r, (mark, value.extractLsb' 0 160)) ∈ draws)
    (query : Query) (answer : BitVec 256) (flag : Bool) :
    ∀ m r value, (cache.cacheQuery query answer) (indexInput m r) = some value →
      ∃ mark, (indexInput m r, (mark, value.extractLsb' 0 160)) ∈
        draws ++ [(query,(flag,answer.extractLsb' 0 160))] := by
  intro m r value present
  by_cases same : indexInput m r = query
  · rw [same, QueryCache.cacheQuery_self] at present
    cases present
    exact ⟨flag, List.mem_append.mpr (Or.inr (by simp only [same, List.mem_singleton]))⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ same] at present
    obtain ⟨mark, member⟩ := old m r value present
    exact ⟨mark, List.mem_append_left _ member⟩

 theorem Provenance.public_fresh {nonces : Message → Bytes 32}
    {cache : QueryCache HashSpec} {history : History} {draws : List Draw}
    (p : Provenance nonces cache history draws) (query : Query) (answer : BitVec 256)
    (miss : cache query = none) (message : Message) (nonce : Bytes 32)
    (parsed : parse query = some (message,nonce)) :
    Provenance nonces (cache.cacheQuery query answer) (recordPublic history query false answer)
      (draws ++ [(query,(false,answer.extractLsb' 0 160))]) := by
  constructor
  · change _ = (recordParsed history query (parse query) (decide _) false answer).indexTrace
    rw [parsed, parsed_trace_fresh, List.map_append, p.trace]
    rfl
  · intro m r value present
    by_cases same : indexInput m r = query
    · rw [same, QueryCache.cacheQuery_self] at present
      cases present
      exact ⟨false, List.mem_append.mpr (Or.inr (by simp only [same, List.mem_singleton]))⟩
    · rw [QueryCache.cacheQuery_of_ne _ _ same] at present
      obtain ⟨mark, member⟩ := p.cached m r value present
      exact ⟨mark, List.mem_append_left _ member⟩
  · intro m member
    rw [public_messages] at member
    rcases p.signed m member with hit | ⟨value, present, member⟩
    · exact Or.inl (hit.public query false answer)
    · right
      have different : indexInput m (nonces m) ≠ query := by
        intro same
        rw [same, miss] at present
        cases present
      exact ⟨value, by rw [QueryCache.cacheQuery_of_ne _ _ different]; exact present,
        List.mem_append_left _ member⟩

 theorem Provenance.public_other {nonces : Message → Bytes 32}
    {cache : QueryCache HashSpec} {history : History} {draws : List Draw}
    (p : Provenance nonces cache history draws) (query : Query) (answer : BitVec 256)
    (parsed : parse query = none) :
    Provenance nonces (cache.cacheQuery query answer) (recordPublic history query false answer) draws := by
  have different := (parse_none_iff query).mp parsed
  constructor
  · change _ = (recordParsed history query (parse query) (decide _) false answer).indexTrace
    rw [parsed, parsed_trace_none]
    exact p.trace
  · intro m r value present
    rw [QueryCache.cacheQuery_of_ne _ _ (different m r)] at present
    exact p.cached m r value present
  · intro m member
    rw [public_messages] at member
    rcases p.signed m member with hit | ⟨value, present, member⟩
    · exact Or.inl (hit.public query false answer)
    · exact Or.inr ⟨value, by rw [QueryCache.cacheQuery_of_ne _ _ (different m (nonces m))]; exact present, member⟩

theorem Provenance.sign_hit {nonces : Message → Bytes 32}
    {cache : QueryCache HashSpec} {history : History} {draws : List Draw}
    (p : Provenance nonces cache history draws) (covered : NonceCovered cache history)
    (message : Message) (answer : BitVec 256)
    (present : cache (indexInput message (nonces message)) = some answer) :
    Provenance nonces cache (recordSign history message true answer) draws := by
  constructor
  · exact p.trace
  · exact p.cached
  · intro m member
    rcases Finset.mem_insert.mp member with same | old
    · subst m
      by_cases known : message ∈ history.signedMessages
      · exact p.signed message known
      · left
        exact ⟨message, first_sign_hit covered message (nonces message) known
          (by rw [present]; exact Option.some_ne_none _)⟩
    · exact p.signed m old

 theorem Provenance.sign_fresh {nonces : Message → Bytes 32}
    {cache : QueryCache HashSpec} {history : History} {draws : List Draw}
    (p : Provenance nonces cache history draws) (message : Message) (answer : BitVec 256)
    (miss : cache (indexInput message (nonces message)) = none)
    (fresh : message ∉ history.signedMessages) :
    Provenance nonces (cache.cacheQuery (indexInput message (nonces message)) answer)
      (recordSign history message false answer)
      (draws ++ [(indexInput message (nonces message), (true, answer.extractLsb' 0 160))]) := by
  constructor
  · change (draws ++ [(indexInput message (nonces message), (true, answer.extractLsb' 0 160))]).map Prod.snd =
      history.indexTrace ++ [(decide (message ∉ history.signedMessages), answer.extractLsb' 0 160)]
    rw [List.map_append, p.trace]
    simp only [List.map_cons, List.map_nil, decide_eq_true fresh]
  · exact @cached_fill cache draws p.cached (indexInput message (nonces message)) answer true
  · intro m member
    rcases Finset.mem_insert.mp member with same | old
    · subst m
      exact Or.inr ⟨answer, QueryCache.cacheQuery_self cache (indexInput message (nonces message)) answer,
        List.mem_append.mpr (Or.inr (List.mem_singleton_self _))⟩
    · rcases p.signed m old with hit | ⟨value, present, member⟩
      · exact Or.inl hit
      · right
        exact ⟨value, cache_fill_preserves cache (indexInput message (nonces message)) answer miss
          (indexInput m (nonces m)) value present, List.mem_append_left _ member⟩

 theorem Provenance.keygen {nonces : Message → Bytes 32}
    {cache : QueryCache HashSpec} {history : History} {draws : List Draw}
    (p : Provenance nonces cache history draws) :
    Provenance nonces cache (recordKeygen history) draws := by
  exact ⟨p.trace, p.cached, p.signed⟩

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorIndexContact.Provenance.sign_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Provenance.sign_fresh
end SigGolfCandidate.Hypertree.SecurityMonitorIndexContact
