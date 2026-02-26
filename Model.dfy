module Model {
  export reveals *
  // --------------------------------------------------
  // Types
  // --------------------------------------------------
  type State = string // parameterize later: type State(==, !new)
  type Message = string // parameterize later: type Message(==, !new)
  
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
    const Q: set<State>
    const qinit: State
    const delta: set<Transition>
    ghost predicate Valid() { 
      Q != {} && 
      qinit in Q && 
      forall t :: t in delta ==> t.from in Q && t.target in Q}

    constructor(q0: State, s: set<State>, d: set<Transition>)
      requires q0 in s && s != {} && forall t :: t in d ==> t.from in s && t.target in s
      ensures Valid()
    {
      qinit := q0;
      Q := s;
      delta := d;
    }
  }

  // --------------------------------------------------
  // Wait-Only
  // --------------------------------------------------
  predicate IsActive(p: Proc, q: State)
    requires q in p.Q
  {
    forall t :: t in p.delta && t.from == q ==> !IsRecv(t.message)
  }

  predicate IsWaiting(p: Proc, q: State)
    requires q in p.Q
  {
    exists t2 :: t2 in p.delta && t2.from == q && IsRecv(t2.message) && forall t :: t in p.delta && t.from == q ==> !IsSend(t.message)
  }

  predicate WaitOnly(p: Proc)
    requires p.Valid()
  {
    IsActive(p,p.qinit) && forall q :: q in p.Q ==> IsActive(p, q) || IsWaiting(p, q)
  }

  // --------------------------------------------------
  // Computations
  // --------------------------------------------------
  method ComputeActiveStates(p: Proc) returns  (states: set<State>)
    requires p.Valid() && WaitOnly(p)
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
    requires p.Valid() && WaitOnly(p)
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