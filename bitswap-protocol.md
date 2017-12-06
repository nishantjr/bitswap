```{pipe='tee bitswap-protocol.maude'}
mod BITSWAP-PROTOCOL is
    protecting QID-SET .
    protecting NAT .

    sort NodeId .
    subsort Qid < NodeId .
    sort Node  .

    op  < name: _ , want-list: _ , have-list: _ >
      : NodeId QidSet QidSet -> Node  [ctor].

    vars A B : NodeId .
    vars N M T T' : Nat .
    vars P Q R S  : QidSet .
    eq < name: A , want-list: P , have-list: Q >
       < name: A , want-list: P , have-list: Q >
     = < name: A , want-list: P , have-list: Q > .
    eq < name: A , want-list: P , have-list: Q >
       < name: A , want-list: R , have-list: S >
     = err [owise] .


    sort Ledger .
    op { owner: _
       , partner: _
       , bytes-sent: _
       , bytes-received: _
       , timestamp: _
       }
    : NodeId NodeId Nat Nat Nat -> Ledger [ctor]
    .

    sort Msg .
    op open : Ledger -> Msg  [ctor].

    sort MsgList .
    subsort Msg < MsgList .
    op .MsgList : -> MsgList [ctor] .
    op _ _ : MsgList MsgList -> MsgList [ctor id: .MsgList assoc] .

    sort Channel Topology .
    subsort Channel Node < Topology .
    op [ _ -> _ | _ ]
     : NodeId NodeId  MsgList -> Channel .

    sort Topology .
    op empty :                   -> Topology .
    op err   :                   -> Topology .
    op _ _   : Topology Topology -> Topology [ctor assoc comm id: empty ] .

    vars ML : MsgList .
    rl  < name: A , want-list: P, have-list: Q >
        [ B -> A | open({ owner: B      , partner: A
                        , bytes-sent: N , bytes-received: M
                        , timestamp: T
                        }) ML ]
     => < name: A
        , want-list: P
        , have-list: Q >
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

