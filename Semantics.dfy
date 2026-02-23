include "Model.dfy"

module Clique {
  import opened Model
  // --------------------------------------------------
  // MODULE: Semantics considering complete graphs Kn
  // -------------------------------------------------

  trait CliqueSemantics {
    const p: Proc
    var v: map<nat, State>
    method Step(m: Message)
      requires p.Valid()
      modifies this
  }

  predicate Sendable(p: Proc, m: Message, q: State) {
    exists t :: t in p.delta && t.from == q && t.message == Send(m)
  }

  predicate Receivable(p: Proc, m: Message, q: State) {
    exists t :: t in p.delta && t.from == q && t.message == Recv(m)
  }

  // --------------------------------------------------
  // Reliable Broadcast
  // --------------------------------------------------

  class ReliableBroadcast extends CliqueSemantics{
    constructor(process: Proc, n: nat)
        requires n > 0
      {
        p := process;
        var v:map<nat,State> := map[];
        for i:nat := 1 to n {
          v := v[i := process.qinit];
        }
      }

    method Step(m: Message)
      requires p.Valid()
      modifies this
    {
      var v' := v;
      if exists i: nat :: i in v && Sendable(p, m, v[i]) {
        // One process in the clique broadcasts m
        var i :| i in v && Sendable(p, m, v[i]);
        var t :| t in p.delta && t.from == v[i] && t.message == Send(m);
        v' := v[i := t.target];
        // Rest of the clique receives m
        for j := 1 to |v|
          invariant v'.Keys == v.Keys
        {
          if j != i && j in v {
            if exists t2 :: t2 in p.delta && t2.from == v[j] && t2.message == Recv(m) {
              var t2 :| t2 in p.delta && t2.from == v[j] && t2.message == Recv(m);
              v' := v'[j := t2.target];
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
}