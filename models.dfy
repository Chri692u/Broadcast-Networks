module Models {

  // --------------------------------------------------
  // Types
  // --------------------------------------------------
  type State(==,!new)
  type Message(==,!new)
  
  datatype Action =
    | Send(m: Message)
    | Recv(m: Message)

  datatype Transition = Transition(from: State, message: Action, target: State)


  predicate IsRecv(a: Action) {
    match a
      case Recv(_) => true
      case Send(_) => false
  }

  predicate IsSend(a: Action) {
    match a
      case Recv(_) => false
      case Send(_) => true
  }

  // --------------------------------------------------
  // Process type
  // --------------------------------------------------
  class Proc {
    var Q: set<State>
    var qinit: State
    var delta: set<Transition>

    constructor(q0: State, states: set<State>, d: set<Transition>)
      requires q0 in states
    {
      qinit := q0;
      Q := states;
      delta := d;
    }
  }

  // --------------------------------------------------
  // Wait-Only predicates
  // --------------------------------------------------
  predicate IsActive(p: Proc, q: State)
    requires q in p.Q
    reads p
  {
    forall t :: t in p.delta && t.from == q ==> !IsRecv(t.message)
  }

  predicate IsWaiting(p: Proc, q: State)
    requires q in p.Q
    reads p
  {
    exists t2 :: t2 in p.delta && t2.from == q && IsRecv(t2.message) && forall t :: t in p.delta && t.from == q ==> !IsSend(t.message)
  }

  predicate WaitOnly(p: Proc)
    reads p
  {
    forall q :: q in p.Q ==> IsActive(p, q) || IsWaiting(p, q)
  }

  method ComputeActiveStates(p: Proc) returns  (states: set<State>)
    requires WaitOnly(p)
    ensures forall q :: q in states && q in p.Q ==> IsActive(p, q) 
  {
    states := {};
    var checked := p.Q;
    while (checked != {})
      invariant forall q :: q in states && q in p.Q ==> IsActive(p, q)
      decreases checked
    {
      var q :| q in checked;
      if (IsActive(p, q)){
        states := states + { q };
      }
      checked := checked - { q };
    }
  }

  method ComputeWaitingStates(p: Proc) returns  (states: set<State>)
    requires WaitOnly(p)
    ensures forall q :: q in states && q in p.Q ==> IsWaiting(p, q)
  {
    states := {};
    var checked := p.Q;
    while (checked != {})
      invariant forall q :: q in states && q in p.Q ==> IsWaiting(p, q)
      decreases checked
    {
      var q :| q in checked;
      if (IsWaiting(p, q)){
        states := states + { q };
      }
      checked := checked - { q };
    }
  }
}