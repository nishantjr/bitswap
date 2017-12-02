```{pipe='tee bitswap-protocol.maude'}
mod BITSWAP-PROTOCOL is
    protecting QID-SET .
    protecting NAT .

    sort NodeId .
    subsort Qid < NodeId .
    sort Node NodeSet .
    subsort Node < NodeSet .

    op  < name: _ , want-list: _ , have-list: _ >
      : NodeId QidSet QidSet -> Node  [ctor].
    op .NodeSet : -> NodeSet .
    op err      : -> NodeSet .
    op _ _ : NodeSet NodeSet -> NodeSet [ctor assoc comm id: .NodeSet ] .

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

    sort Channel ChannelSet .
    subsort Channel < ChannelSet .
    op [ _ -> _ | _ ]
     : NodeId NodeId  MsgList -> Channel .

    sort Topology .
    op _ _
     : NodeSet ChannelSet -> Topology .


endm
```

Basic tests for `NodeSet`s:

-   Idempotency:

    ``` {pipe="maude 2>&1 -no-banner bitswap-protocol"}
    rewrite
        < name: 'a , want-list: M:QidSet, have-list: N:QidSet >
        < name: 'a , want-list: M:QidSet, have-list: N:QidSet >
     == < name: 'a , want-list: M:QidSet, have-list: N:QidSet > .
    ```

-   Detecting duplicate nodes:

    ```{pipe='maude 2>&1 -no-banner bitswap-protocol'}
    rewrite
        < name: 'a , want-list: 'a , have-list: N:QidSet >
        < name: 'a , want-list: 'b , have-list: N:QidSet >
     == err .
     ```
   ```