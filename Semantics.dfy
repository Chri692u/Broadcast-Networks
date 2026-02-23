// --------------------------------------------------
// MODULE: Semantics considering complete graphs
// -------------------------------------------------
include "Model.dfy"

module Clique {
  import opened Model
  class CliqueBroadcast {
    const p: Proc
    var v: map<nat, State>

    constructor(process: Proc, clique: nat)
      requires clique > 0
    {
        p := process;
        var v:map<nat,State> := map[];
        for i:nat := 1 to clique {
            v := v[i := process.qinit];
        }
    }
  }
  // --------------------------------------------------
  // Reliable Broadcast
  // --------------------------------------------------
  
  // --------------------------------------------------
  // Unreliable Broadcast
  // --------------------------------------------------
}