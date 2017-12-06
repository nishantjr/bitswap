We describe the basic messages and data-structures involved:

```{pipe='tee bitswap-protocol.maude'}
mod BITSWAP-PROTOCOL is
    protecting QID-SET .
    protecting NAT .
```

`Node`s are peers in the BitSwap network:

```{pipe='tee -a bitswap-protocol.maude'}
    sort NodeId .
    subsort Qid < NodeId .
    sort Node  .
    op  < name: _ , want-list: _ , have-list: _ >
      : NodeId QidSet QidSet -> Node  [ctor].
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
    op open : Ledger -> Msg  [ctor].
```


We assume out communication channels do *not* re-order messages:

```{pipe='tee -a bitswap-protocol.maude'}
    sort MsgList .
    subsort Msg < MsgList .
    op .MsgList : -> MsgList [ctor] .
    op _ _ : MsgList MsgList -> MsgList [ctor id: .MsgList assoc] .

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

    vars A B : NodeId .
    vars N M T T' : Nat .
    vars P Q R S  : QidSet .
```

A `Topology` may *not* have two nodes with the same name:

```{pipe='tee -a bitswap-protocol.maude'}
    eq < name: A , want-list: P , have-list: Q >
       < name: A , want-list: P , have-list: Q >
     = < name: A , want-list: P , have-list: Q > .
    eq < name: A , want-list: P , have-list: Q >
       < name: A , want-list: R , have-list: S >
     = err [owise] .
```

`Nodes` accept the `open` message:

```{pipe='tee -a bitswap-protocol.maude'}
    vars ML : MsgList .
    rl  < name: A , want-list: P, have-list: Q >
        [ B -> A | open({ owner: B      , partner: A
                        , bytes-sent: N , bytes-received: M
                        , timestamp: T
                        }) ML ]
     => < name: A
        , want-list: P
        , have-list: Q
        >
        [ B -> A | ML ] .
endm
```

Basic tests for `Topology`s:

-   Idempotency:

    ``` {pipe="maude 2>&1 -no-banner bitswap-protocol"}
    reduce
        < name: 'a , want-list: M:QidSet, have-list: N:QidSet >
        < name: 'a , want-list: M:QidSet, have-list: N:QidSet >
     == < name: 'a , want-list: M:QidSet, have-list: N:QidSet > .
    ```

-   Detecting duplicate nodes:

    ```{pipe='maude 2>&1 -no-banner bitswap-protocol'}
    reduce
        < name: 'a , want-list: 'a , have-list: N:QidSet >
        < name: 'a , want-list: 'b , have-list: N:QidSet >
     == err .
     ```

-  Check that the open message is received:

    ```{pipe='maude 2>&1 -no-banner bitswap-protocol'}
    rewrite
        < name: 'a , want-list: ('p, 'q), have-list: ('x, 'y) >
        [ 'b -> 'a | open({ owner: 'b     , partner: 'a
                          , bytes-sent: 3 , bytes-received: 5
                          , timestamp: 0
                          }) ML:MsgList ]
    .
    ```

