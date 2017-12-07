We describe the basic messages and data-structures involved:

```{pipe='tee bitswap-protocol.maude'}
mod BITSWAP-PROTOCOL is
    protecting QID-SET .
    protecting NAT .
```

`Node`s are peers in the BitSwap network, with their `Strategy`
defining how they interact with their peers:

```{pipe='tee -a bitswap-protocol.maude'}
    sort NodeId .
    sort Strategy .
    subsort Qid < NodeId .
    sort Node  .
    op  < name: _
        , strategy: _
        , want-list: _
        , have-list: _
        >
      : NodeId Strategy QidSet QidSet -> Node  [ctor].
```

The `Ledger` is used both as a record for keeping track
of the connection state between nodes, and a part of the
`open` message:

```{pipe='tee -a bitswap-protocol.maude'}
    sort Ledger .
    op { owner: _
       , partner: _
       , bytes-sent: _
       , bytes-received: _
       , timestamp: _
       }
    : NodeId NodeId Nat Nat Nat -> Ledger [ctor]
    .
```

We define messages:

```{pipe='tee -a bitswap-protocol.maude'}
    sort Msg .
    op open      : Ledger -> Msg  [ctor] .
    op want-list : QidSet -> Msg  [ctor] .
    op block     : Qid    -> Msg  [ctor] .
```

Since we assume our communication channels do *not* re-order messages,
we use lists to represent them. Unfortunately, the unification algorithm
does not support `assoc` with `id`, we work around it:

```{pipe='tee -a bitswap-protocol.maude'}
    sort MsgList .
    subsort Msg < MsgList .
    op .MsgList : -> MsgList [ctor] .
    op _ _      : MsgList MsgList -> MsgList [ctor assoc] .
    eq .MsgList .MsgList = .MsgList .
    eq .MsgList X:Msg = X:Msg .MsgList .
```

A `Channel` transmits messages in one direction reliably:

```{pipe='tee -a bitswap-protocol.maude'}
    sort Channel .
    op [ _ -> _ | _ ] : NodeId NodeId  MsgList -> Channel .

```

`Topology`s are sets of `Node`s and `Channel`s between them:

```{pipe='tee -a bitswap-protocol.maude'}
    sort Topology .
    subsort Channel Node < Topology .
    op empty :                   -> Topology .
    op err   :                   -> Topology .
    op _ _   : Topology Topology -> Topology [ctor assoc comm id: empty ] .

    vars A : NodeId .
    vars P Q R S  : QidSet .
    vars STRAT    : Strategy .
```

A `Topology` may *not* have two nodes with the same name:

```{pipe='tee -a bitswap-protocol.maude'}
    eq < name: A , strategy: STRAT, want-list: P , have-list: Q >
       < name: A , strategy: STRAT, want-list: P , have-list: Q >
     = < name: A , strategy: STRAT, want-list: P , have-list: Q > .
    eq < name: A , strategy: STRAT, want-list: P , have-list: Q >
       < name: A , strategy: STRAT, want-list: R , have-list: S >
     = err [owise] .
endm

```

We implement the `naive` strategy, where `Node`s don't keep
track of `Ledger`s and send data to anyone who requests it:

```{pipe='tee -a bitswap-protocol.maude'}
mod BITSWAP-NAIVE is
    including BITSWAP-PROTOCOL .
    op naive : -> Strategy .

    vars ML ML'   : MsgList .
    vars A B      : NodeId .
    vars N M T T' : Nat .
    vars P Q R S  : QidSet .

    rl  < name: A , strategy: naive, want-list: P, have-list: Q >
        [ B -> A | open({ owner: B      , partner: A
                        , bytes-sent: N , bytes-received: M
                        , timestamp: T
                        }) ML ]
        [ A -> B | ML' ]
     => < name: A
        , strategy: naive
        , want-list: P
        , have-list: Q
        >
        [ B -> A | ML ]
        [ A -> B | ML' want-list(P) ]
    .

    rl  < name: A , strategy: naive
        , want-list: P
        , have-list: (X:NeQidSet , S) >
        [ B -> A | want-list((X:NeQidSet , R)) ML ]
        [ A -> B | ML' ]
     => < name: A
        , strategy: naive
        , want-list: P
        , have-list: X:NeQidSet,S
        >
        [ B -> A | ML ]
        [ A -> B | ML' block(X:NeQidSet) ]
    .
endm
```

Basic tests for `Topology`s:

-   Idempotency:

    ``` {pipe="maude 2>&1 -no-banner bitswap-protocol"}
    reduce
        < name: 'a , strategy: S:Strategy, want-list: M:QidSet, have-list: N:QidSet >
        < name: 'a , strategy: S:Strategy, want-list: M:QidSet, have-list: N:QidSet >
     == < name: 'a , strategy: S:Strategy, want-list: M:QidSet, have-list: N:QidSet > .
    ```

-   Detecting duplicate nodes:

    ```{pipe='maude 2>&1 -no-banner bitswap-protocol'}
    reduce
        < name: 'a , strategy: S:Strategy, want-list: 'a , have-list: N:QidSet >
        < name: 'a , strategy: S:Strategy, want-list: 'b , have-list: N:QidSet >
     == err .
     ```

Let's watch what happens when we let the protocol play out:

```{pipe='maude 2>&1 -no-banner bitswap-protocol'}
rewrite
    < name: 'a , strategy: naive, want-list: ('p, 'q), have-list: ('x, 'y) >
    < name: 'b , strategy: naive, want-list: ('x, 'q), have-list: ('p, 'y) >
    [ 'b -> 'a | open({ owner: 'b     , partner: 'a
                      , bytes-sent: 3 , bytes-received: 5
                      , timestamp: 0
                      })
                      .MsgList ]
    [ 'a -> 'b | open({ owner: 'a     , partner: 'b
                      , bytes-sent: 5 , bytes-received: 3
                      , timestamp: 0
                      })
                      .MsgList ]
.
```

