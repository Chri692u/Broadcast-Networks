include "Model.dfy"
include "Semantics.dfy"
import opened Model
import opened Clique

// This example builds a leader selection procedure for reliable broadcast: When "m" is broadcasted, 1 process moves to q_isolated and n-1 processes move to q_err
method Main(){
    var n := 5;
    print "This example builds a leader selection procedure for reliable broadcast: When 'm' is broadcasted, 1 process moves to q_isolated and n-1 processes move to q_err \n";
    var states: set<State> := {"q_0", "q_isolated", "q_err"};
    var transitions: set<Transition> := {
        Transition("q_0", Send("m"), "q_isolated"),
        Transition("q_0", Recv("m"), "q_err")
    };
    var p := new Proc("q_0", states, transitions); 
    var netR := new ReliableBroadcast(p, n);
    netR.Step("m");
    var netU := new UnreliableBroadcast(p, n);
    netU.Step("m");
    print "Leader selection for n=5:\n";
    print "Process states after Step(\"m\"):\n";
    var pid := 0;
    while pid <= |netR.v.Keys|
    {
        if pid in netR.v.Keys{
            print "Process ", pid, " -> ", netR.v[pid], "\n";
        }
        pid := pid + 1;
    }
    // NB. This breaks when we are unreliable.
    print "Leader selection breaks for unreliable:\n";
    print "Process states after Step(\"m\"):\n";
    pid := 0;
    while pid <= |netU.v.Keys|
    {
        if pid in netU.v.Keys{
            print "Process ", pid, " -> ", netU.v[pid], "\n";
        }
        pid := pid + 1;
    }
    
}