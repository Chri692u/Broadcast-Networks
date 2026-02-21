module Models {

  type State(==)
  type Message(==)

  datatype Action =
    | Send(m: Message)
    | Recv(m: Message)

  class Proc {
    var Q: set<State>
    var qinit: State
    var delta: set<(State, Action, State)>

    constructor(states: set<State>, q0: State, d: set<(State, Action, State)>)
      requires q0 in states
      requires forall t :: t in d ==> t.0 in states && t.2 in states
    {
      Q := states;
      qinit := q0;
      delta := d;
    }
  }
}