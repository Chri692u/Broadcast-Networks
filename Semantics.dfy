include "Model.dfy"

module Clique {
  import opened Model
  export reveals *
  // --------------------------------------------------
  // MODULE: Semantics considering complete graphs Kn
  // -------------------------------------------------

  trait CliqueSemantics {
    const p: Proc
    var v: map<nat, State>
    method Step(m: Message)
      modifies this
  }

  predicate Sendable(p: Proc, m: Message, q: State) {
    exists t :: t in p.delta && t.from == q && t.message == Send(m)
  }

  predicate ExistsReceiverIn(network: CliqueSemantics, i: nat, m: Message)
    requires i in network.v.Keys
    reads network
  {
    exists t' :: t' in network.p.delta && t'.from == network.v[i] && t'.message == Recv(m)
  }

  // --------------------------------------------------
  // Reliable Broadcast
  // --------------------------------------------------

  class ReliableBroadcast extends CliqueSemantics{
    constructor(process: Proc, n: nat)
      requires n > 0 && process.Valid()
    {
      p := process;
      var tmp: map<nat, State> := map[];
      for i:nat := 1 to n+1 {
        tmp := tmp[i := process.qinit];
      }
      v := tmp;
    }

    method Step(m: Message)
      modifies this
    {
      var v' := v;
      if exists i: nat :: i in v && Sendable(p, m, v[i]) {
        // One process in the clique broadcasts m
        var i :| i in v && Sendable(p, m, v[i]);
        var t :| t in p.delta && t.from == v[i] && t.message == Send(m);
        v' := v[i := t.target];
        // Rest of the clique receives m
        for j := 1 to |v|+1
          invariant v'.Keys == v.Keys
        {
          if j != i && j in v {
            if ExistsReceiverIn(this, j, m) {
              var t' :| t' in p.delta && t'.from == v[j] && t'.message == Recv(m);
              v' := v'[j := t'.target];
            }
          }
        }
        // Commit updates
        v := v';
      }
    }
  }

  // --------------------------------------------------
  // Unreliable Broadcast
  // --------------------------------------------------
  class UnreliableBroadcast extends CliqueSemantics{
    constructor(process: Proc, n: nat)
      requires n > 0 && process.Valid()
    {
      p := process;
      var tmp: map<nat, State> := map[];
      for i:nat := 1 to n+1 {
        tmp := tmp[i := process.qinit];
      }
      v := tmp;
    }
    
    method Step(m: Message)
      modifies this
    {
      var v' := v;
      if exists i: nat :: i in v && Sendable(p, m, v[i]) {
        // One process in the clique broadcasts m
        var i :| i in v && Sendable(p, m, v[i]);
        var t :| t in p.delta && t.from == v[i] && t.message == Send(m);
        v' := v[i := t.target];
        // Rest of the clique receives m or ignores
        for j := 1 to |v|+1
          invariant v'.Keys == v.Keys
        {
          if j != i && j in v {
            if ExistsReceiverIn(this, j, m) {
              var ignore?: bool :| ignore? in {false, true}; // Bug, the SMT-solver picks one value for the entire example we need to find another way
              var t' :| t' in p.delta && t'.from == v[j] && t'.message == Recv(m);
              if ignore? {
                v' := v'[j := t'.target];
              }
            }
          }
        }
        // Commit
        v := v';
      }
    }
  }
}