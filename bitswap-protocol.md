```{pipe='tee -a bitswap-protocol.maude'}
fmod BITSWAP-BUFFER is
    protecting QID-SET .

```

We use sets of quoted identifiers to opaquely represent blocks:

```{pipe='tee -a bitswap-protocol.maude'}
    sorts Block BlockSet .
    subsort Qid < Block .
    subsort QidSet < BlockSet .

```


Since we assume our communication channels do *not* re-order messages,
we use lists to represent them. Unfortunately, the unification algorithm
does not support `assoc` with `id`, we work around it:

```{pipe='tee -a bitswap-protocol.maude'}
    sort Msg .
    sort NodeId .
    sort MsgList .
    subsort Msg < MsgList .
    op .MsgList : -> MsgList [ctor] .
    op _ _      : MsgList MsgList -> MsgList [ctor assoc] .
    eq .MsgList .MsgList = .MsgList .
    eq .MsgList X:Msg = X:Msg .MsgList .
```

A `Buffer` represents buffers in hosts, or in the network -- anywhere where bandwidth is limited:

```{pipe='tee -a bitswap-protocol.maude'}
    sort Buffer .
    op [ _ -> _ | _ ] : NodeId NodeId  MsgList -> Buffer [ctor] .

endfm

view Buffer from TRIV to BITSWAP-BUFFER is
    sort Elt to Buffer .
endv

```

`Node`s are peers in the BitSwap network, with their `Strategy`
defining how they interact with their peers:

```{pipe='tee -a bitswap-protocol.maude'}
fmod BITSWAP-NODE is
    protecting BITSWAP-BUFFER .
    protecting SET{Buffer} * (sort Set{Buffer} to BufferSet ) .

    sort Strategy .
    subsort Qid < NodeId .
    sort Node  .
    op  < name: _
        , strategy: _
        , want-list: _
        , have-list: _
        , conns: _
        >
      : NodeId Strategy BlockSet BlockSet BufferSet -> Node  [ctor] .
```

```{pipe='tee -a bitswap-protocol.maude'}

endfm

```

`Topology`s are an AC soup of `Node`s:

```{pipe='tee -a bitswap-protocol.maude'}
fmod BITSWAP-TOPOLOGY is
    protecting BITSWAP-NODE .
    sort Topology .
    subsort Node < Topology .
    op empty :                   -> Topology .
    op _ _   : Topology Topology -> Topology [ctor assoc comm id: empty ] .
    op err   :                   -> Topology .

    vars A : NodeId .
    vars P Q R S  : QidSet .
    vars STRAT    : Strategy .
    vars BL BL'   : BufferSet .
    vars TOPO     : Topology .
```

A `Topology` may *not* have two nodes with the same name:

```{pipe='tee -a bitswap-protocol.maude'}
    eq < name: A , strategy: STRAT, want-list: P , have-list: Q , conns: BL  >
       < name: A , strategy: STRAT, want-list: P , have-list: Q , conns: BL  >
     = < name: A , strategy: STRAT, want-list: P , have-list: Q , conns: BL  > .
    eq < name: A , strategy: STRAT, want-list: P , have-list: Q , conns: BL  >
       < name: A , strategy: STRAT, want-list: R , have-list: S , conns: BL' >
     = err [owise] .

endfm

```

```{pipe='tee -a bitswap-protocol.maude'}
fmod BITSWAP-MESSAGES is
    protecting BITSWAP-BUFFER .
    protecting NAT .
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
    op open      : Ledger -> Msg  [ctor] .
    op want-list : QidSet -> Msg  [ctor] .
    op block     : Qid    -> Msg  [ctor] .
endfm

```


```{pipe='tee -a bitswap-protocol.maude'}
mod BITSWAP-PROTOCOL is
    protecting BITSWAP-MESSAGES .
    protecting BITSWAP-TOPOLOGY .

    vars STRAT    : Strategy .
    vars STRAT'   : Strategy .
    vars ML ML'   : MsgList .
    vars BL BL'   : BufferSet .
    vars MSG MSG' : Msg .
    vars A B      : NodeId .
    vars N M T T' : Nat .
    vars P Q R S  : QidSet .
```

Nodes open connections to each other:

```{pipe='tee -a bitswap-protocol.maude'}
    op #connExists : NodeId NodeId BufferSet -> Bool .

   crl < name: A, strategy: STRAT , want-list: P, have-list: Q , conns: BL >
       < name: B, strategy: STRAT', want-list: R, have-list: S , conns: BL' >
    => < name: A, strategy: STRAT , want-list: P, have-list: Q , conns: BL >
       < name: B, strategy: STRAT', want-list: R, have-list: S , conns: [ A -> B | .MsgList ], BL' >
    if #connExists(A, B, BL') == false
   .
   crl < name: A, strategy: STRAT , want-list: P, have-list: Q , conns: BL >
       < name: B, strategy: STRAT', want-list: R, have-list: S , conns: BL' >
    => < name: A, strategy: STRAT , want-list: P, have-list: Q , conns: [ A -> B | .MsgList ], BL >
       < name: B, strategy: STRAT', want-list: R, have-list: S , conns: BL' >
    if #connExists(A, B, BL) == false
    .

    eq #connExists(A, B, ([ A -> B | ML ], BL)) = true .
    eq #connExists(A, B,                   BL ) = false [owise] .
```

For now, we messages from one `Node`'s buffer are tranfered instantly to other `Node`s

```{pipe='tee -a bitswap-protocol.maude'}

    rl < name: A, strategy: STRAT , want-list: P, have-list: Q , conns: [ A -> B | MSG ML  ], BL  >
       < name: B, strategy: STRAT', want-list: R, have-list: S , conns: [ A -> B | ML'     ], BL' >
    => < name: A, strategy: STRAT , want-list: P, have-list: Q , conns: [ A -> B | ML      ], BL  >
       < name: B, strategy: STRAT', want-list: R, have-list: S , conns: [ A -> B | ML' MSG ], BL' >
       .

```

We implement the `naive` strategy, where `Node`s don't keep
track of `Ledger`s and send data to anyone who requests it:

```{pipe='tee -a bitswap-protocol.maude'}
    op naive : -> Strategy .

    rl  < name: A , strategy: naive, want-list: P, have-list: Q
        , conns: [ B -> A | open({ owner: B
                   , partner: A
                   , bytes-sent: N , bytes-received: M
                   , timestamp: T
                   }) ML ]
               , [ A -> B | ML' ]
        >
     => < name: A
        , strategy: naive
        , want-list: P
        , have-list: Q
        , conns: [ B -> A | ML ]
               , [ A -> B | ML' want-list(P) ]
        >
    .

    rl  < name: A , strategy: naive
        , want-list: P
        , have-list: (X:Qid , S)
        , conns: [ B -> A | want-list((X:Qid , R)) ML ]
               , [ A -> B | ML' ]
        >
     => < name: A
        , strategy: naive
        , want-list: P
        , have-list: X:Qid,S
        , conns: [ B -> A | ML ]
               , [ A -> B | ML' block(X:Qid) ]
        >
    .
   crl  < name: A , strategy: naive
        , want-list: P, have-list: S
        , conns: [ B -> A | want-list(R) ML ]
               , [ A -> B | ML' ]
        >
     => < name: A , strategy: naive
        , want-list: P, have-list: S
        , conns: [ B -> A | ML ]
               , [ A -> B | ML']
        >
    if intersection(R, S) == empty
    .

    rl  < name: A , strategy: naive
        , want-list: (X:NeQidSet, P)
        , have-list: S
        , conns:  [ B -> A | block((X:NeQidSet, R)) ML ]
               ,  [ A -> B | ML' ]
        >
     => < name: A
        , strategy: naive
        , want-list: P
        , have-list: X:NeQidSet,S
        , conns: [ B -> A | ML ]
               , [ A -> B | ML']
        >
    .

endm
```

Basic tests for `Topology`s:

-   Idempotency:

    ``` {pipe="maude 2>&1 -no-banner bitswap-protocol"}
    reduce in BITSWAP-TOPOLOGY :
        < name: 'a , strategy: S:Strategy, want-list: M:QidSet, have-list: N:QidSet, conns: BL >
        < name: 'a , strategy: S:Strategy, want-list: M:QidSet, have-list: N:QidSet, conns: BL >
     == < name: 'a , strategy: S:Strategy, want-list: M:QidSet, have-list: N:QidSet, conns: BL > .
    ```

-   Detecting duplicate nodes:

    ```{pipe='maude 2>&1 -no-banner bitswap-protocol'}
    reduce in BITSWAP-TOPOLOGY :
        < name: 'a , strategy: S:Strategy, want-list: 'a , have-list: N:QidSet, conns: BL >
        < name: 'a , strategy: S:Strategy, want-list: 'b , have-list: N:QidSet, conns: BL >
     == err .
    ```

-   ```{pipe='maude 2>&1 -no-banner bitswap-protocol  | sed "s/</\n    </g" '}
    unify
       < name: A,  strategy: STRAT , want-list: P ,       have-list: Q ,       conns: [ A -> B   | MSG ML  ],  BL  >
    =? < name: 'a, strategy: naive,  want-list: ('p, 'q) ,have-list: ('x, 'y) ,conns: (['a -> 'b | open({owner: 'a,partner: 'b,bytes-sent: 5, bytes-received: 3,timestamp: 0}) .MsgList], ['b -> 'a | .MsgList]) >
       .
    unify
       < name: A,  strategy: STRAT , want-list: P ,    have-list: Q ,    conns: [ A -> B  | MSG ML  ],  BL  >
       < name: B,  strategy: STRAT', want-list: R ,    have-list: S ,    conns: [ A -> B  | ML'     ],  BL' >
    =? < name: 'a, strategy: naive,  want-list: 'p, 'q,have-list: 'x, 'y,conns: ['a -> 'b | open({owner: 'a,partner: 'b,bytes-sent: 5, bytes-received: 3,timestamp: 0}) .MsgList ], ['b -> 'a | .MsgList] >
       < name: 'b, strategy: naive,  want-list: 'q, 'x,have-list: 'p, 'y,conns: ['a -> 'b | .MsgList], ['b -> 'a | open({owner: 'b,partner: 'a,bytes-sent: 3, bytes-received: 5,timestamp: 0}) .MsgList] >
       .
    unify < name: A , strategy: naive
        , want-list: P
        , have-list: (X:Qid , S)
        , conns: [ B -> A | want-list((X:Qid , R)) ML ]
               , [ A -> B | ML' ]
        >
    =? < name: 'b,
    strategy: naive,want-list: 'q, 'x,have-list: 'p, 'y,conns: ['a -> 'b |
    want-list(('p, 'q)) block('x) .MsgList], ['b -> 'a | .MsgList] >
    .
    ```

Let's watch what happens when we let the protocol play out:


```{pipe="maude 2>&1 -no-banner bitswap-protocol | sed 's/</\n    </g'"}
rewrite [30]
    < name: 'a , strategy: naive, want-list: ('p, 'q), have-list: ('x, 'y)
    , conns:  [ 'a -> 'b | open({ owner: 'a     , partner: 'b
                                , bytes-sent: 5 , bytes-received: 3
                                , timestamp: 0}) .MsgList ]>
    < name: 'b , strategy: naive, want-list: ('x, 'q), have-list: ('p, 'y)
    , conns: [ 'b -> 'a | open({ owner: 'b     , partner: 'a
                               , bytes-sent: 3 , bytes-received: 5
                               , timestamp: 0 }) .MsgList ]>
    .
```

\pagebreak

```{pipe='cat bitswap-protocol.maude' .numberLines}
```
