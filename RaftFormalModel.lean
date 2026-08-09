import Lean
import Mathlib.Tactic

-------------------------------------------------
-- STEP 1: MODELING THE LOCAL STATE
-------------------------------------------------

structure LogEntry where
  command : String
  term    : Nat
  deriving Repr, DecidableEq

abbrev Log := List LogEntry

inductive Role
  | follower
  | candidate
  | leader
  deriving Repr, DecidableEq

abbrev PeerMap := List (Nat × Nat)

def PeerMap.get (map : PeerMap) (id : Nat) (default : Nat) : Nat :=
  match map.lookup id with
  | some v => v
  | none   => default

def PeerMap.set (map : PeerMap) (id : Nat) (val : Nat) : PeerMap :=
  (id, val) :: map.filter (fun (k, _) => k != id)

structure LeaderState where
  matchIndex : PeerMap
  nextIndex  : PeerMap
  deriving Repr, DecidableEq

structure PersistentState where
  currentTerm : Nat
  votedFor    : Option Nat
  log         : Log
  deriving Repr, DecidableEq

structure VolatileState where
  commitIndex : Nat
  role        : Role
  leaderState : Option LeaderState
  votesGranted : Nat
  deriving Repr, DecidableEq

structure NodeState where
  volatile : VolatileState
  persist  : PersistentState
  id       : Nat
  h_commit_bounds : volatile.commitIndex ≤ persist.log.length
  deriving Repr, DecidableEq

def newNode (id : Nat) : NodeState :=
 {
    id  := id,
    persist := {
      currentTerm := 0,
      log         := [],
      votedFor    := none,
    },
    volatile := {
      commitIndex := 0,
      role        := .follower,
      leaderState := none,
      votesGranted := 0,
    },
    h_commit_bounds := by rfl
  }

-------------------------------------------------
-- STEP 2: THE APPEND-ENTRIES RPC & LOGIC
-------------------------------------------------

-- The Message Protocol
inductive RPC
  | appendEntries (term : Nat)
                  (leaderId : Nat)
                  (prevLogIndex : Nat)
                  (prevLogTerm : Nat)
                  (entries : Log)
                  (leaderCommit : Nat)
  | appendReply   (followerId : Nat)
                  (term : Nat)
                  (success : Bool)
                  (matchIndex : Nat)
  | requestVote   (node : NodeState)
                  (candidateId : Nat)
                  (candidateTerm : Nat)
                  (lastLogIdx : Nat)
                  (lastLogTerm : Nat)
  | requestReply  (term : Nat)
                  (voteGranted : Bool)
  deriving Repr, DecidableEq

-- The Follower's Logic: Returns (NewState, ReplyMessage)
def handleAppendEntries
  (node : NodeState) (term : Nat) (_leaderId : Nat)
  (prevLogIndex : Nat) (prevLogTerm : Nat)
  (entries : Log) (leaderCommit : Nat) : NodeState × Bool :=
  -- Step 1 & 2: Reject if the term is stale or the prefix term doesn't match.
  -- prevLogIndex acts as our prefix length constraint.
  if hopt: node.persist.currentTerm > term   ||
     node.persist.log.length < prevLogIndex ||
     prevLogIndex < node.volatile.commitIndex ||
     (prevLogIndex > 0 &&
          (node.persist.log[prevLogIndex - 1]?).map (·.term) != some prevLogTerm) then
    (node, false)
  else
     -- Step 3 & 4: Splice the log.
     -- List.take naturally isolates the 0-indexed prefix using our absolute length count.
     have: ¬ (prevLogIndex < node.volatile.commitIndex) := by grind
     let newLog := node.persist.log.take prevLogIndex ++ entries
     -- Step 5: If leaderCommit > commitIndex,
     -- set commitIndex = min(leaderCommit, index of last new entry).
     let lastNewIndex := prevLogIndex + entries.length
     let newCommitIndex :=
       if leaderCommit > node.volatile.commitIndex then
         min leaderCommit lastNewIndex
       else
         node.volatile.commitIndex
     ({ node with
         persist := { node.persist with
           log         := newLog,
           currentTerm := term,
         },
         volatile := { node.volatile with
           commitIndex := newCommitIndex
         },
         h_commit_bounds := by grind
      }, true)

-- Helper: Recursively find the highest log index that has been replicated to a majority
-- of the cluster AND belongs to the current term.
def findNewCommitIndex (log : Log) (matchIdxMap : PeerMap) (clusterIds : List Nat)
                       (leaderId : Nat) (currentTerm : Nat) (commitIndex : Nat)
                       (N : Nat) (majority : Nat) : Nat :=
  if N <= commitIndex then
    commitIndex -- We've hit the old commit index; nothing new to commit.
  else
    -- Tally how many nodes have replicated at least up to index N
    let count := clusterIds.foldl (fun c id =>
      if id == leaderId then
        c + 1 -- The leader always has its own entries
      else if PeerMap.get matchIdxMap id 0 >= N then
        c + 1
      else
        c
    ) 0
    -- Check if the entry at N belongs to the current term
    -- (Log is 0-indexed, so absolute length N is index N-1)
    let isCurrentTerm := match log[N - 1]? with
                         | some entry => entry.term == currentTerm
                         | none       => false
    if count >= majority && isCurrentTerm then
      N -- Found the new highest commit index!
    else
      -- Step down and try the next index
      findNewCommitIndex log matchIdxMap clusterIds leaderId
                         currentTerm commitIndex (N - 1) majority

def handleAppendReply (node : NodeState) (clusterIds : List Nat)
  (followerId : Nat) (replyTerm : Nat) (success : Bool) (matchIdx : Nat) : NodeState :=
  -- Phase 1: Term Progression
  -- If a follower has a higher term, the leader is deposed.
  if replyTerm > node.persist.currentTerm then
    { node with
      persist := { node.persist with
        currentTerm := replyTerm,
        votedFor    := none
      },
      volatile := { node.volatile with
        role         := Role.follower,
        votesGranted := 0,
        leaderState  := none
      },
      h_commit_bounds := node.h_commit_bounds
    }

  -- Phase 2: Stale Reply or Invalid Role Check
  else if replyTerm < node.persist.currentTerm || node.volatile.role != Role.leader then
    node

  -- Phase 3: Update LeaderState and calculate new CommitIndex
  else
    match node.volatile.leaderState with
    | none => node -- Should mathematically never happen if role is leader
    | some ls =>
        let newLs :=
          if success then
            { matchIndex := PeerMap.set ls.matchIndex followerId matchIdx,
              nextIndex  := PeerMap.set ls.nextIndex followerId (matchIdx + 1) }
          else
            -- If append failed, decrement nextIndex so we can retry with an older prefix
            let currentNext := PeerMap.get ls.nextIndex followerId 1
            let decremented := if currentNext > 1 then currentNext - 1 else 1
            { ls with nextIndex := PeerMap.set ls.nextIndex followerId decremented }

        -- Phase 4: See if we can advance the commitIndex
        let majority := (clusterIds.length / 2) + 1
        let proposedCommit := findNewCommitIndex
                                node.persist.log newLs.matchIndex clusterIds node.id
                                node.persist.currentTerm node.volatile.commitIndex
                                node.persist.log.length majority

        { node with
          volatile := { node.volatile with
            leaderState := some newLs,
            commitIndex := proposedCommit
          },
          h_commit_bounds := by sorry
        }

------------------------------------------------------------
-- STEP 3: THE LOCAL INDUCTIVE PROOF (SAFETY GUARANTEE)
------------------------------------------------------------

theorem take_append_take_drop {α : Type} (a b : ℕ) (l : List α) :
  List.take a l ++ List.take b (List.drop a l) = List.take (a + b) l := by sorry

-- Theorem: If handleAppendEntries is successful, the Follower's
-- new log is a guaranteed prefix of the Leader's log.
theorem append_success_implies_prefix
  (node : NodeState) (term leaderId prevIdx prevTerm : Nat) (entries : Log) (leaderCommit : Nat)
  (h_success :
  (handleAppendEntries node term leaderId prevIdx prevTerm entries leaderCommit).2 = true) :
  let newNode := (handleAppendEntries node term leaderId prevIdx prevTerm entries leaderCommit).1
  newNode.persist.log = node.persist.log.take prevIdx ++ entries := by sorry

------------------------------------------------------------
-- STEP 4: MODELING THE UNRELIABLE NETWORK
------------------------------------------------------------

-- A packet in flight contains its destination and the payload
structure Packet where
  payload : RPC
  destId  : Nat
  deriving Repr, DecidableEq

-- The Global State of the Universe
structure NetworkWorld where
  inflight : List Packet   -- "The Soup" (Non-deterministic, unordered)
  nodes    : Nat → Option NodeState
  clusterIds : List Nat

-- Helper: Update a specific node in the cluster
def updateNode (worldNodes : Nat → Option NodeState) (newNode : NodeState) :
  Nat → Option NodeState :=
    fun id => if id == newNode.id then some newNode else worldNodes id

-- Processes a RequestVote RPC and returns the updated NodeState along with
-- a boolean indicating if the vote was granted.
def handleRequestVote (node : NodeState) (candidateId : Nat) (candidateTerm : Nat)
  (lastLogIdx : Nat) (lastLogTerm : Nat) : NodeState × Bool :=
  -- Phase 1: Term Progression (The "Step Down" rule)
  -- If we see a higher term, we update our term and clear our vote.
  let node' :=
    if candidateTerm > node.persist.currentTerm then
      { node with
        persist := { node.persist with
          currentTerm := candidateTerm,
          votedFor := none
        }
      }
      -- TRACE: we accepted the new term as it is larger.
    else node
  -- Phase 2: Stale Term Check
  if candidateTerm < node'.persist.currentTerm then
    (node', false)
  else
    -- Phase 3: Log Up-To-Date Check
    let myLastTerm :=
      match node'.persist.log[node'.persist.log.length - 1]? with
      | some e => e.term
      | none   => 0
    -- Raft logic: Later term wins.
    -- If terms equal, longer log wins.
    let logIsUpToDate :=
      if lastLogTerm != myLastTerm then
        lastLogTerm > myLastTerm
      else
        lastLogIdx >= node'.persist.log.length
    -- Phase 4: Voting Check
    -- We can vote if we haven't voted yet in this term,
    -- OR if we already voted for this exact candidate.
    let canVoteFor := node'.persist.votedFor == none ||
                      node'.persist.votedFor == some candidateId
    if canVoteFor && logIsUpToDate then
      ({ node' with
         persist := { node'.persist with
           votedFor := some candidateId
         }
      }, true)
    else
      (node', false)

def becomeLeader (node : NodeState) (clusterIds : List Nat) : NodeState :=
  let lastLogIndex      := node.persist.log.length
  let initialNextIndex  := clusterIds.map (fun id => (id, lastLogIndex + 1))
  let initialMatchIndex := clusterIds.map (fun id => (id, 0))
  { node with
    volatile := { node.volatile with
      role := Role.leader,
      leaderState := some {
        nextIndex := initialNextIndex,
        matchIndex := initialMatchIndex
      }
    },
    h_commit_bounds := node.h_commit_bounds
  }

-- Processes a RequestReply (vote response) and returns the updated NodeState.
-- We pass in clusterIds so we can calculate the majority and initialize the leader state.
def handleRequestReply (node : NodeState) (clusterIds : List Nat)
  (replyTerm : Nat) (voteGranted : Bool) : NodeState :=
  -- Phase 1: Term Progression
  -- If the reply contains a term greater than ours, we are out of date.
  -- Step down immediately to follower and update our term.
  if replyTerm > node.persist.currentTerm then
    { node with
      persist := { node.persist with
        currentTerm := replyTerm,
        votedFor    := none
      },
      volatile := { node.volatile with
        role         := Role.follower,
        votesGranted := 0
      }
    }
  -- Phase 2: Stale Reply or Invalid Role Check
  -- If the reply is for an older term, or we are no longer a candidate
  -- (e.g., we already won or lost), just ignore the message.
  else if replyTerm < node.persist.currentTerm || node.volatile.role != Role.candidate then
    node
  -- Phase 3: Tallying Votes
  else if voteGranted then
    let newVoteCount := node.volatile.votesGranted + 1
    let majority := (clusterIds.length / 2) + 1
    -- Did we reach a majority?
    if newVoteCount >= majority then
      -- We won the election! Upgrade to Leader.
      becomeLeader node clusterIds
    else
      -- Still waiting for more votes, just record this one.
      { node with
        volatile := { node.volatile with
          votesGranted := newVoteCount
        }
      }
  -- Phase 4: Vote Denied
  -- If the vote wasn't granted, our state doesn't change.
  else
    node

def process_rpc (w : NetworkWorld) (targetNode : NodeState) (packet : Packet) : NetworkWorld :=
  match packet.payload with
  | RPC.appendEntries t leaderId pIdx pTerm entries leaderCommit =>
      -- 1. Process the local state change and extract the success boolean
      let (updatedNode, success) :=
        handleAppendEntries targetNode t leaderId pIdx pTerm entries leaderCommit
      -- 2. Calculate the matchIndex to report back to the leader
      let matchIdx := if success then pIdx + entries.length else 0
      -- 3. Construct the reply packet directed back to the leader
      let replyPacket : Packet := {
        payload := RPC.appendReply targetNode.id updatedNode.persist.currentTerm success matchIdx,
        destId  := leaderId
      }
      -- 4. Update the world state: save the node, drop the old packet, add the new packet
      { w with
        nodes    := updateNode w.nodes updatedNode,
        inflight := replyPacket :: w.inflight.filter (· != packet) }
  | RPC.requestVote _ candidateId candidateTerm lastLogIdx lastLogTerm =>
      -- 1. Process the local state change (using targetNode, not the payload's node)
      let (updatedNode, success) :=
        handleRequestVote targetNode candidateId candidateTerm lastLogIdx lastLogTerm
      -- 2. Construct the vote reply packet directed back to the candidate
      let replyPacket : Packet := {
        payload := RPC.requestReply updatedNode.persist.currentTerm success,
        destId  := candidateId
      }
      -- 3. Update the world state
      { w with
        nodes    := updateNode w.nodes updatedNode,
        inflight := replyPacket :: w.inflight.filter (· != packet) }
  | RPC.requestReply replyTerm voteGranted =>
      let updatedNode := handleRequestReply targetNode w.clusterIds replyTerm voteGranted
      { w with
        nodes    := updateNode w.nodes updatedNode,
        inflight := w.inflight.filter (· != packet) }
  | RPC.appendReply followerId replyTerm success matchIdx =>
      let updatedNode :=
        handleAppendReply targetNode w.clusterIds followerId replyTerm success matchIdx
      { w with
        nodes    := updateNode w.nodes updatedNode,
        inflight := w.inflight.filter (· != packet) }

-- The Global Transition: Pluck ONE message from the soup and process it
-- This is how we model asynchronous, out-of-order delivery.
def global_step (w : NetworkWorld) (packetToProcess : Packet) : NetworkWorld :=
    match (w.inflight.contains packetToProcess),
          (w.nodes packetToProcess.destId) with
    | true, some targetNode => process_rpc w targetNode packetToProcess
    | _, _                  => w

------------------------------------------------------------------
-- STEP 5: THE GLOBAL INVARIANT (THE CAPSTONE OF SMR)
------------------------------------------------------------------

-- The ultimate property of Raft's Replication logic.
-- "If two nodes have an entry at the same index with the same term,
-- then their logs are identical from that index down to the beginning."
def LogMatchingInvariant (w : NetworkWorld) : Prop :=
  -- For any two nodes in our cluster...
  ∀ (n1 n2 : NodeState), (w.nodes n1.id).isSome → (w.nodes n2.id).isSome →
    ∀ (idx : Nat) (entry1 entry2 : LogEntry),
      n1.persist.log[idx]? = some entry1 →
      n2.persist.log[idx]? = some entry2 →
        entry1.term = entry2.term →
          n1.persist.log.take (idx + 1) =
          n2.persist.log.take (idx + 1)

def IsValidLeaderLog (w : NetworkWorld) (t pIdx pTerm : ℕ) (entries : Log) : Prop :=
  ∃(n : NodeState),
    (w.nodes n.id).isSome ∧
    n.persist.currentTerm ≥ t ∧
    (n.persist.log.drop pIdx).take entries.length = entries ∧
    (pIdx > 0 → ∃ cmd, n.persist.log[pIdx - 1]? = some ⟨cmd, pTerm⟩)

-- 2. Packets in flight must carry valid logs!
def NetworkMatchingInvariant (w : NetworkWorld) : Prop :=
  ∀ (pkt : Packet) (t leaderId pIdx pTerm : Nat) (entries : Log) (leaderCommit : Nat),
    pkt ∈ w.inflight →
    pkt.payload = RPC.appendEntries t leaderId pIdx pTerm entries leaderCommit →
    IsValidLeaderLog w t pIdx pTerm entries

def RaftInvariant (w : NetworkWorld) : Prop :=
  LogMatchingInvariant w ∧ NetworkMatchingInvariant w

------------------------------------------------------------------
-- STEP 6: CLOSING THE CAPSTONE (THE TLA+ ARCHITECTURE)
------------------------------------------------------------------

-- 1. The Initial State Definition
-- The universe starts with empty logs and no messages in flight.
def InitState (w : NetworkWorld) : Prop :=
  ∀ (n: NodeState), (w.nodes n.id).isSome ∧ n.persist.log = [] ∧ w.inflight = []

-- 2. The Trace Evaluator
-- A Trace is just folding the 'global_step' function over a list of packets.
def applyTrace (world : NetworkWorld)
               (trace : List Packet) : NetworkWorld :=
  (trace.foldl global_step world)

theorem map_update_id_eq_self {α : Type}
  (l : List α) (target : α) (idFn : α → ℕ)
  (h_unique : ∀ n ∈ l, idFn n = idFn target → n = target) :
  l.map (fun n ↦ if idFn n = idFn target then target else n) = l := by sorry

-- ===============================================================
-- THE HELPER LEMMAS
-- ===============================================================

-- Lemma A: The Base Case
-- If the system is in the InitState, the invariant is trivially true
-- because there are no logs to mismatch.
theorem raft_init_safe (w : NetworkWorld) (h_init : InitState w) :
  RaftInvariant w := by sorry

theorem raft_step_safe_pIdx_zero
  (w : NetworkWorld) (logIdx : ℕ)
  (updatedState n2 targetNode : NodeState)
  (h_inv : RaftInvariant w)
  (entry1 entry2 : LogEntry)
  (h_entries_are_on_same_term : entry1.term = entry2.term)
  (t leaderId pTerm : ℕ) (entries : Log) (leaderCommit : ℕ) (packet : Packet)
  (hentry1_exists : updatedState.persist.log[logIdx]? = some entry1)
  (hentry2_exists : n2.persist.log[logIdx]? = some entry2)
  (hn2_belongs : (w.nodes n2.id).isSome)
  (packetinflight : packet ∈ w.inflight)
  (hpayload : packet.payload = RPC.appendEntries t leaderId 0 pTerm entries leaderCommit)
  (h : targetNode.volatile.commitIndex ≤ entries.length)
  (h_append : { volatile := { commitIndex := targetNode.volatile.commitIndex,
                              role := targetNode.volatile.role,
                              leaderState := targetNode.volatile.leaderState,
                              votesGranted := targetNode.volatile.votesGranted },
                persist := {
                  currentTerm := t,
                  log := List.take 0 targetNode.persist.log ++ entries,
                  votedFor := targetNode.persist.votedFor,
                },
                id := targetNode.id,
                h_commit_bounds := by
                  simpa only [List.take_zero, List.nil_append] using h
              } = updatedState) :
  List.take (logIdx + 1) updatedState.persist.log = List.take (logIdx + 1) n2.persist.log := by
    sorry

theorem raft_step_safe_updated_node_vs_old_node
(logIdx pIdx : ℕ) (updatedState : NodeState)
(n1 : NodeState) (n2 : NodeState) (hoptn1 : n1 = updatedState)
(hoptn2 : ¬n2 = updatedState) (h_inv : RaftInvariant w)
(entry1 entry2 : LogEntry)
(h_entries_are_on_same_term : entry1.term = entry2.term)
(hentry1_exists : n1.persist.log[logIdx]? = some entry1)
(hentry2_exists : n2.persist.log[logIdx]? = some entry2)
(targetNode : NodeState) (htn_belongs : (w.nodes targetNode.id).isSome)
(hn2_belongs : (w.nodes n2.id).isSome)
(t leaderId pTerm leaderCommit : Nat) (entries : Log)
(h_append : handleAppendEntries targetNode t leaderId pIdx pTerm entries leaderCommit =
(updatedState, true))
: List.take (logIdx + 1) n1.persist.log = List.take (logIdx + 1) n2.persist.log := by sorry

theorem handleAppendEntries_preserves_LogMatching
  (w : NetworkWorld)
  (pkt : Packet)
  (h_inv : RaftInvariant w)
  (targetNode : NodeState)
  (hinflight_contains_pkt : w.inflight.contains pkt = true)
  (htarget_node_exists : w.nodes pkt.destId = some targetNode)
  (t leaderId pIdx pTerm leaderCommit : ℕ)
  (entries : Log)
  (payload : pkt.payload = RPC.appendEntries t leaderId pIdx pTerm entries leaderCommit) :
  LogMatchingInvariant { w with
    inflight := List.filter (fun x ↦ x != pkt) w.inflight,
    nodes := updateNode w.nodes
             (handleAppendEntries targetNode t leaderId pIdx pTerm entries leaderCommit).1
  } := by sorry

theorem handleAppendEntries_preserves_NetworkMatching
  (w : NetworkWorld)
  (pkt : Packet)
  (h_inv : RaftInvariant w)
  (targetNode : NodeState)
  (hinflight_contains_pkt : w.inflight.contains pkt = true)
  (htarget_node_exists : w.nodes pkt.destId = some targetNode)
  (t leaderId pIdx pTerm leaderCommit : ℕ)
  (entries : Log)
  (payload : pkt.payload = RPC.appendEntries t leaderId pIdx pTerm entries leaderCommit) :
  NetworkMatchingInvariant
    { w with
      inflight := List.filter (fun x ↦ x != pkt) w.inflight,
      nodes := updateNode w.nodes
               (handleAppendEntries targetNode t leaderId pIdx pTerm entries leaderCommit).1 } := by
      sorry

theorem raft_step_safe_process_packet (w : NetworkWorld)
(pkt : Packet) (h_inv : RaftInvariant w) (targetNode : NodeState)
(hinflight_contains_pkt : w.inflight.contains pkt = true)
(htarget_node_exists : w.nodes pkt.destId = some targetNode) :
RaftInvariant (process_rpc w targetNode pkt) := by sorry

-- If the invariant holds now, ONE step of the network will preserve it.
-- THIS the `append_success_implies_prefix` theorem is used!
theorem raft_step_safe (w : NetworkWorld) (pkt : Packet) (h_inv : RaftInvariant w) :
  RaftInvariant (global_step w pkt) := by sorry

-- ===============================================================
-- THE CAPSTONE THEOREM
-- ===============================================================

-- First, we prove that if the step is safe, an arbitrary trace is safe.
theorem invariant_preserved_over_trace (w : NetworkWorld) (trace : List Packet)
  (h_inv : RaftInvariant w) :
  RaftInvariant (applyTrace w trace) := by sorry

-- Finally, the ultimate Raft Safety Theorem:
-- A system starting from InitState remains safe across ANY possible network trace.
theorem raft_is_safe (w : NetworkWorld) (trace : List Packet)
  (h_init : InitState w) :
  RaftInvariant (applyTrace w trace) := by sorry

theorem term_monotonicity
  (node : NodeState) (cId cTerm lIdx lTerm : Nat) :
  let (newState, _) := handleRequestVote node cId cTerm lIdx lTerm
  newState.persist.currentTerm ≥ node.persist.currentTerm := by sorry

theorem no_double_voting
  (node : NodeState) (cA cB term lIdx lTerm : Nat) (h_diff : cA ≠ cB) :
  let (stateAfterA, grantedA) := handleRequestVote node cA term lIdx lTerm
  grantedA = true →
  let (_, grantedB) := handleRequestVote stateAfterA cB term lIdx lTerm
  grantedB = false := by sorry

theorem vote_implies_log_freshness
  (node : NodeState) (cId cTerm lIdx lTerm : Nat) :
  let (_, granted) := handleRequestVote node cId cTerm lIdx lTerm
  granted = true →
  -- The candidate's last term must be greater than ours, OR
  -- the terms are equal and the candidate's log is at least as long as ours.
  (let myLastTerm := match node.persist.log[(node.persist.log.length - 1)]? with
                     | some e => e.term
                     | none   => 0
   lTerm > myLastTerm ∨ (lTerm = myLastTerm ∧ lIdx ≥ node.persist.log.length)) := by sorry

theorem requestVote_preserves_log
  (node : NodeState) (candidateId candidateTerm lastLogIdx lastLogTerm : Nat) :
  (handleRequestVote node candidateId candidateTerm lastLogIdx lastLogTerm).1.persist.log =
  node.persist.log := by
    sorry

-- The Operations the client cares about
inductive OpType
  | read  (k : String)
  | write (k : String) (v : Nat)
  deriving Repr, DecidableEq

-- A trace consists of requests sent and responses received
inductive Event
  | invoke   (procId : Nat) (op     : OpType)
  | complete (procId : Nat) (result : Option Nat)
  -- None indicates a timeout/partition
  deriving Repr, DecidableEq

abbrev History := List Event

-- The Reference Implementation (Atomic Dictionary)
abbrev KVState := List (String × Nat)

-- The Pure Logic of the data structure
def step (s : KVState)
         (op : OpType) : (KVState × Option Nat) :=
  match op with
  | OpType.write k v => ((k, v) :: s, some v)
  | OpType.read k =>
      let val := s.find? (fun (k', _) => k' == k)
      (s, val.map Prod.snd)

-- Validating that a given execution trace is legally possible
def isValidSequence (s : KVState)
                    (ops : List (OpType × Option Nat)) : Bool :=
  match ops with
  | [] => true
  | (op, observedResult) :: rest =>
      let (newState, computedResult) := step s op
-- The Check: Did the distributed system return what the
-- single-threaded model predicted?
      if observedResult == computedResult then
        isValidSequence newState rest
      else
        false

-- The mathematical justification for dropping data during a partition
theorem uncommitted_data_is_ephemeral
  (node : NodeState) (idx : Nat)
  (h : node.volatile.commitIndex = 0) :
  idx > node.volatile.commitIndex →
  -- It is possible for a valid Raft transition
  -- (like receiving AppendEntries with a higher term)
  -- to safely overwrite or drop this log entry.
  ∃ (newState : NodeState) (term leaderId prevIdx prevTerm leaderCommit : Nat) (entries : Log),
    (handleAppendEntries node term leaderId prevIdx prevTerm entries leaderCommit).1 = newState ∧
    newState.persist.log.length < idx := by sorry
