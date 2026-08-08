# Lean 4 Raft Consensus Model

This repository contains a structural model of the Raft consensus algorithm written in Lean 4. Raft is a consensus algorithm for managing a replicated log.

This model is deliberately structured to reflect the primary design goal of Raft itself: understandability. Rather than weaving network topology, state transitions, and safety properties into a single complex block, the file decomposes the consensus problem into independent subproblems. This mirrors the state-machine and trace-based evaluation often seen in TLA+ specifications.

## Why is the File Structured This Way?

The architecture of this formalization is broken down into six sequential steps. This approach abstracts away the complexities of distributed systems into manageable, verifiable pieces:

### 1. Modeling the Local State

Before a network can exist, a node must exist. The model begins by defining the isolated state of a single server. In Raft, servers are always in one of three states: leader, follower, or candidate. The `NodeState` structure strictly separates persistent storage (which must survive crashes) from volatile state (which is reinitialized). This matches the exact state requirements necessary to ensure safe recovery and term progression.

### 2. The Append-Entries RPC & Logic

Raft uses a stronger form of leadership than other consensus algorithms, meaning log entries only flow in one direction: from the leader to the other servers. The `RPC` inductive type and `handleAppendEntries` function encapsulate this. By separating the local message-handling logic from the network transmission, we can independently verify that a single node reacts correctly to a message (e.g., rejecting stale terms or splicing logs) without worrying about how that message arrived.

### 3. Local Inductive Proofs

This section defines the local safety guarantees. Even though the theorems (like `append_success_implies_prefix`) are currently stubbed, their presence in the structure is vital. They act as "contracts." By separating local proofs from global proofs, we establish that if a single node follows the rules of `handleAppendEntries`, its individual log is a guaranteed prefix of the leader's log, setting the foundation for global consensus.

### 4. Modeling the Unreliable Network (The "Soup")

Distributed systems must ensure safety under all non-Byzantine conditions, including network delays, partitions, packet loss, duplication, and reordering.

* **The `NetworkWorld`:** We model the network as an unordered list of `Packet` objects (the "soup").
* **Asynchrony:** The `global_step` function plucks a single, arbitrary message from this soup and applies it to a target node.
* **Decoupling:** This design forces our system to prove safety against completely non-deterministic, out-of-order execution rather than relying on a perfectly ordered queue.

### 5. The Global Invariant

This is the capstone of the Replicated State Machine (RSM). The `LogMatchingInvariant` and `NetworkMatchingInvariant` definitions mathematically formalize Raft's core safety properties. For instance, Raft guarantees that if two logs contain an entry with the same index and term, then the logs are identical in all entries up through the given index. Defining these invariants globally ensures that the isolated logic from Steps 1 and 2 aggregates correctly across the entire cluster.

### 6. The TLA+ Architecture & Trace Evaluator

The final step defines the universe's `InitState` and the `applyTrace` fold. This is inspired by TLA+ verification techniques. Instead of attempting to prove the system safe at all times instantly, the architecture is set up to prove that starting from a valid `InitState`, any arbitrary list of network packets (a trace) processed by `global_step` will preserve the `RaftInvariant`.

## Current Status

This file currently serves as a **structural specification** of the Raft algorithm. The theorems and helper lemmas are outlined and mapped to the core safety guarantees detailed in raft.pdf, but the mathematical proofs (the `sorry` blocks) are left unimplemented for now. The current focus is on clearly defining the state space, the message protocol, and the transition boundaries of the distributed system.

## Reference

*In Search of an Understandable Consensus Algorithm (Extended Version)* by Diego Ongaro and John Ousterhout.
