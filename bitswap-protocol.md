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

    vars A B : NodeId .
    vars N M T T' : Nat .
endm
```

```{pipe='maude 2>&1 -no-banner bitswap-protocol'}
rewrite
  < name: 'a , want-list: M:QidSet, have-list: N:QidSet >
  [ 'b -> 'a | open({ owner: 'b     , partner: 'a
                    , bytes-sent: 4 , bytes-received: 5
                    , timestamp: 0
                    }) ]
  .
```
