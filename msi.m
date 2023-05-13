----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  ProcCount: 3;          -- number processors
  ValueCount:   2;       -- number of data values.
  ReqVC: 0;		-- low priority
	FwdVC: 1;		
	AckVC: 2;		-- high priority
  QMax: 2;
  NumVCs: AckVC - ReqVC + 1;
  NetMax: ProcCount*3;
  

----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
type
  Proc: scalarset(ProcCount);   -- unordered range of processors
  Value: scalarset(ValueCount); -- arbitrary values for tracking coherence
  Home: enum { HomeType };      -- need enumeration for IsMember calls
  Node: union { Home , Proc };

  VCType: ReqVC..NumVCs-1;

  MessageType: enum {  ReadReq,         -- request for shared state
                       FwdReadReq,      -- get data from remote
                       ReadAck,         -- read ack (w/ icount)
                       FwdReadAck,      -- forwarded read ack
		                   ReadFwd,         -- forwarded read data

		                   WriteReq,        -- write request
                       FwdWriteReq,     -- invalidate remote
                       WriteAck,        -- write ack (w/ icount)
                       FwdWriteAck,     -- forwarded write ack
		                   WriteFwd,        -- forwarded write data
                      
		                   WBReq,           -- writeback request (w/ or wo/ data)
                       WBAck,           -- writeback ack      
                       WBStaleReadAck,  -- wb ack, but wb was stale due to rd
                       WBStaleWriteAck, -- wb ack, but wb was stale due to wr
 
                       RInvReq,         -- remote invalidation req
                       RIAck            -- ack remote invalidation

                    };

  Message:
    Record
      mtype: MessageType;
      src: Node;
      -- don't need a destination for verification
      vc: VCType;
      aux: Node;  -- forwarding msgs
      cnt: 0..ProcCount;
      val: Value;
    End;

  HomeState:
    Record
      state: enum { HM, HS, HI, TMM, TMS };
      owner: Node;	
      pending_node: Node;
      sharers: multiset [ProcCount] of Node; 
      val: Value;
    End;

  ProcState:
    Record
      state: enum { PM, PS, PI,
                    TIS, TIL,         -- I to S and S to I
		                IM, IIM, TRIS, TRIF, TMI, TMII, TWIS, TWIF,    
                                       -- I to M and M to I
                    TSM, TAM, TRIM, TISM, TIAM
                                       -- S to M and M to S                               
                  };
      acount: 0..ProcCount;
      icount: 0..ProcCount;
      val: Value; 
    End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
  HomeNode:  HomeState;
  Procs: array [Proc] of ProcState;
  Net:   array [Node] of multiset [NetMax] of Message;
  InBox: array [Node] of array [VCType] of Message; -- If a message is not processed, it is placed in InBox, blocking that virtual channel
  msg_processed: boolean;
  LastWrite: Value; -- Used to confirm that writes are not lost; this variable would not exist in real hardware

----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------
Procedure Send(mtype:MessageType;
	       dst:Node;
	       src:Node;
         vc:VCType;
	       aux:Node;
         cnt:0..ProcCount;
         val:Value;
         );
         
var msg:Message;
Begin
  Assert (MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages";
  msg.mtype := mtype;
  msg.src   := src;
  msg.vc    := vc;
  msg.aux   := aux;
  msg.cnt   := cnt;
  msg.val   := val;
  MultiSetAdd(msg, Net[dst]);
End;

Procedure ErrorUnhandledMsg(msg:Message; n:Node);
Begin
  switch msg.mtype
  case WriteReq, ReadReq, WBReq:
    msg_processed := false;
  else
    error "Unhandled message type!";
  endswitch;
End;

Procedure ErrorUnhandledState();
Begin
  error "Unhandled state!";
End;

Procedure AddToSharersList(n:Node);
Begin
  if MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) = 0
  then
    MultiSetAdd(n, HomeNode.sharers);
  endif;
End;

Procedure RemoveFromSharersList(n:Node);
Begin
  MultiSetRemovePred(i:HomeNode.sharers, HomeNode.sharers[i] = n);
End;

Procedure SendRInvReqToSharers(rqst:Node);
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      if n != rqst
      then 
        Send(RInvReq, n, HomeType, ReqVC, rqst, UNDEFINED, UNDEFINED);
      endif;
      RemoveFromSharersList(n);
    endif;
  endfor;
End;

Procedure HomeReceive(msg:Message);
var cnt:0..ProcCount;
var cnthack:0..1;
Begin
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at home -- "; put HomeNode.state;

  -- compiler barfs if we put this inside the switch
  cnt := MultiSetCount(i:HomeNode.sharers, true);

  if MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = msg.src) != 0
  then 
    cnthack := 1;
  else
    cnthack := 0;
  endif;

  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  switch HomeNode.state
  case HI:
    Assert (cnt = 0) "Sharers list non-empty, but line is Invalid";

    switch msg.mtype

    case ReadReq:
      HomeNode.state := HS;
      AddToSharersList(msg.src);
      Send(ReadAck, msg.src, HomeType, AckVC, UNDEFINED, UNDEFINED, HomeNode.val);

    case WriteReq:
      HomeNode.state := HM;
      HomeNode.owner := msg.src;
      Send(WriteAck, msg.src, HomeType, AckVC, UNDEFINED, cnt, HomeNode.val); -- cnt is zero

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HM:
    Assert (IsUndefined(HomeNode.owner) = false) 
       "HomeNode has no owner, but line is Modified"; 

    switch msg.mtype

    case ReadReq:
      HomeNode.state := TMS;
      HomeNode.pending_node := msg.src;
      Send(FwdReadReq, HomeNode.owner, HomeType, FwdVC, msg.src, UNDEFINED, UNDEFINED);
      
    case WriteReq:
      HomeNode.state := TMM;
      HomeNode.pending_node := msg.src;
      Send(FwdWriteReq, HomeNode.owner, HomeType, FwdVC, msg.src, UNDEFINED, UNDEFINED);
      
    case WBReq:
      HomeNode.state := HI;
      HomeNode.val   := msg.val;
      LastWrite := HomeNode.val;
      Send(WBAck, msg.src, HomeType, AckVC, UNDEFINED, UNDEFINED, UNDEFINED);
      undefine HomeNode.owner;
      undefine HomeNode.pending_node;

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HS:
    Assert (cnt != 0) "sharers list empty, but line is shared";

    switch msg.mtype

    case ReadReq:
      AddToSharersList(msg.src);
      Send(ReadAck, msg.src, HomeType, AckVC, UNDEFINED, UNDEFINED, HomeNode.val);

    case WriteReq:
      HomeNode.state := HM;
      Send(WriteAck, msg.src, HomeType, AckVC, UNDEFINED, cnt-cnthack,HomeNode.val);        
      SendRInvReqToSharers(msg.src); -- removes sharers, too
      HomeNode.owner := msg.src;
      
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case TMS:
    switch msg.mtype

    case FwdReadAck:
      HomeNode.state := HS;
      AddToSharersList(msg.src);
      AddToSharersList(HomeNode.pending_node);
      HomeNode.val   := msg.val;
      LastWrite := HomeNode.val;
      undefine HomeNode.owner;
      undefine HomeNode.pending_node;
    
    case WBReq:
      Assert (!IsUnDefined(HomeNode.pending_node)) "pending_node undefined";
      HomeNode.state := HS;
      AddToSharersList(HomeNode.pending_node);
      HomeNode.val   := msg.val;
      LastWrite := HomeNode.val;
      Send(WBStaleReadAck, msg.src, HomeType, AckVC, UNDEFINED, UNDEFINED, UNDEFINED);
      undefine HomeNode.owner;
      undefine HomeNode.pending_node;
    
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;
      
  case TMM:
    switch msg.mtype

    case FwdWriteAck:
      Assert (!IsUnDefined(HomeNode.pending_node)) "pending_node undefined";
      HomeNode.state := HM;
      HomeNode.owner := HomeNode.pending_node;
      undefine HomeNode.pending_node;

    case WBReq:
      if HomeNode.owner = msg.src
      then
        -- old owner
        Assert (!IsUnDefined(HomeNode.pending_node)) "pending_node undefined";
        Send(WBStaleWriteAck, msg.src, HomeType, AckVC, UNDEFINED, UNDEFINED, UNDEFINED);
        HomeNode.val   := msg.val;
        --LastWrite := HomeNode.val;
        HomeNode.state := HM;
        HomeNode.owner := HomeNode.pending_node;
        undefine HomeNode.pending_node;
      elsif HomeNode.pending_node = msg.src
      then
        -- new owner, queue or nack
	      msg_processed := false;
      else
        error "WBReq from unexpected node";
      endif;

    else
      ErrorUnhandledMsg(msg, HomeType);
    
    endswitch;

  endswitch;

End;

Procedure ProcReceive(msg:Message; p:Proc);
Begin
--  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
--  put " at proc "; put p; put "\n";

  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  alias ps:Procs[p].state do
  alias pv:Procs[p].val do --renew value

  switch ps

  case PI:

    switch msg.mtype
    case RInvReq:
      Send(RIAck, msg.aux, p, AckVC, UNDEFINED, UNDEFINED, UNDEFINED);
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PM:

    switch msg.mtype
    case FwdWriteReq:
      Send(FwdWriteAck, HomeType, p, AckVC, UNDEFINED, UNDEFINED, pv);
      Send(WriteFwd, msg.aux, p, AckVC, UNDEFINED, UNDEFINED, pv);
      undefine pv;
      ps := PI;
    case FwdReadReq:
      Send(FwdReadAck, HomeType, p, AckVC, UNDEFINED, UNDEFINED, pv);
      Send(ReadFwd, msg.aux, p, AckVC, UNDEFINED, UNDEFINED, pv);
      ps := PS;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PS:

    switch msg.mtype
    case RInvReq:
      Send(RIAck, msg.aux, p, AckVC, UNDEFINED, UNDEFINED, UNDEFINED);
      undefine pv;
      ps := PI;-- changed
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;


  ----------------------------                         
  -- I/S interaction states
  ----------------------------
  case TIS:

    switch msg.mtype
    case ReadAck, ReadFwd:
      ps := PS;
      pv := msg.val;
    case RInvReq:
      Send(RIAck, msg.aux, p, AckVC, UNDEFINED, UNDEFINED, UNDEFINED);
      ps := TIL;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TIL:
   
    switch msg.mtype
    case ReadAck, ReadFwd:
      undefine pv;
      ps := PI;
    case RInvReq:
      Send(RIAck, msg.aux, p, AckVC, UNDEFINED, UNDEFINED, UNDEFINED);
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;
  ----------------------------
  -- I/M interaction states
  ----------------------------
  case IM:
    switch msg.mtype
    case WriteFwd:
      ps := PM;
      pv := msg.val;
      LastWrite := pv;
    case WriteAck:
      Procs[p].icount := msg.cnt;
      pv := msg.val;
      if Procs[p].acount = Procs[p].icount
      then
	      ps := PM;
        LastWrite := pv;
	      undefine Procs[p].acount;
	      undefine Procs[p].icount;
      else
        ps := IIM;
      endif;
    case RIAck:
      Procs[p].acount := Procs[p].acount + 1;
    case RInvReq:
      Send(RIAck, msg.aux, p, AckVC, UNDEFINED, UNDEFINED, UNDEFINED);
    case FwdReadReq, FwdWriteReq:
      msg_processed := false;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case IIM:
    switch msg.mtype
    case RIAck:
      Procs[p].acount := Procs[p].acount + 1;
      -- we've already received the WriteAck, so go to M if acount = icount
      if Procs[p].acount = Procs[p].icount
      then
	      ps := PM;
        LastWrite := pv;
	      undefine Procs[p].acount;
	      undefine Procs[p].icount;
      endif;
    case FwdReadReq, FwdWriteReq:
      msg_processed := false;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TMI:
    switch msg.mtype
    case WBAck:
      undefine pv;
      ps := PI;
    case RInvReq:
      Send(RIAck, msg.aux, p, AckVC, UNDEFINED, UNDEFINED, UNDEFINED);
      ps := TMII;
    case WBStaleReadAck:
      ps := TRIS;
    case FwdReadReq:
      Send(ReadFwd, msg.aux, p, AckVC, UNDEFINED, UNDEFINED, pv);
      ps := TRIF;
    case WBStaleWriteAck:
      ps := TWIS;
    case FwdWriteReq:
      Send(WriteFwd, msg.aux, p, AckVC, UNDEFINED, UNDEFINED, pv);
      ps := TWIF;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TMII:
    switch msg.mtype
    case WBAck:
      undefine pv;
      ps := PI;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TRIS:
    switch msg.mtype
    case FwdReadReq:
      ps := PI;
      Send(ReadFwd, msg.aux, p, AckVC, UNDEFINED, UNDEFINED, pv);
      undefine pv;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TRIF:
    switch msg.mtype
    case WBStaleReadAck:
      undefine pv;
      ps := PI;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TWIS:
    switch msg.mtype
    case FwdWriteReq:
      ps := PI;
      Send(WriteFwd, msg.aux, p, AckVC, UNDEFINED, UNDEFINED, pv);
      undefine pv;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TWIF:
    switch msg.mtype
    case WBStaleWriteAck:
      undefine pv;
      ps := PI;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  ----------------------------
  -- S/M interaction states
  ----------------------------

  case TSM:
    switch msg.mtype
    case WriteFwd:
      ps := PM;
      pv := msg.val;
      LastWrite := pv;
    case RIAck:
      Procs[p].acount := Procs[p].acount + 1;
      ps := TISM;
    case RInvReq:
      Send(RIAck, msg.aux, p, AckVC, UNDEFINED, UNDEFINED, UNDEFINED);
      ps := TRIM;
    case WriteAck:
      ps := TAM;
    case FwdReadReq, FwdWriteReq:
      msg_processed := false;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TAM:
    switch msg.mtype
    case RIAck:
      Procs[p].acount := Procs[p].acount + 1;
      if Procs[p].acount = Procs[p].icount
      then
	      ps := PM;
        LastWrite := pv;
	      undefine Procs[p].acount;
	      undefine Procs[p].icount;
      endif;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TRIM:
    switch msg.mtype
    case WriteFwd:
      ps := PM;
      pv := msg.val;
      LastWrite := pv;
    case FwdReadReq, FwdWriteReq:
      msg_processed := false;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TISM:
    switch msg.mtype
    case RIAck:
      Procs[p].acount := Procs[p].acount + 1;
    case WriteAck:
      Procs[p].icount := msg.cnt;
      if Procs[p].acount = Procs[p].icount
      then
	      ps := PM;
        LastWrite := pv;
	      undefine Procs[p].acount;
	      undefine Procs[p].icount;
      else
        ps := TIAM;
      endif;
    case FwdReadReq, FwdWriteReq:
      msg_processed := false;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case TIAM:
    switch msg.mtype
    case RIAck:
      Procs[p].acount := Procs[p].acount + 1;
      if Procs[p].acount = Procs[p].icount
      then
	      ps := PM;
        LastWrite := pv;
	      undefine Procs[p].acount;
	      undefine Procs[p].icount;
      endif;
    case FwdReadReq, FwdWriteReq:
      msg_processed := false;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;
  
  ----------------------------
  -- Error catch
  ----------------------------
  else
    ErrorUnhandledState();

  endswitch;

  endalias;
  endalias;
End;

----------------------------------------------------------------------
-- Rules
----------------------------------------------------------------------

-- Processor actions (affecting coherency)
ruleset n:Proc do
  alias p:Procs[n] do

  ruleset v:Value Do
  	rule "store new value"
   	 (p.state = PM)
    	==>
 		   p.val := v;      
 		   LastWrite := v;
  	endrule;
	endruleset;

  rule "read request"
    (p.state = PI)
  ==>
    Send(ReadReq, HomeType, n, ReqVC, UNDEFINED, UNDEFINED, UNDEFINED);
    p.state := TIS;
  endrule;

  rule "write request"
    (p.state = PI)
  ==>
    Send(WriteReq, HomeType, n, ReqVC, UNDEFINED, UNDEFINED, UNDEFINED);
    p.state := IM;
    clear p.acount;
    clear p.icount;
  endrule;

  rule "upgrade request"
    (p.state = PS)
  ==>
    Send(WriteReq, HomeType, n, ReqVC, UNDEFINED, UNDEFINED, UNDEFINED);
    p.state := IM;  
    clear p.acount;
    clear p.icount;
  endrule;

  rule "writeback"
    (p.state = PM)
  ==>
    Send(WBReq, HomeType, n, ReqVC, UNDEFINED, UNDEFINED, p.val);
    p.state := TMI;
  endrule;

  rule "evict"
    (p.state = PS)
  ==>
    undefine p.val;
    p.state := PI;
  endrule;

  endalias;
endruleset;

-- receive rules
ruleset n:Node do
  choose midx:Net[n] do
    alias chan:Net[n] do
    alias msg:chan[midx] do

    rule "receive"
      (msg.vc = AckVC) |
      (msg.vc = FwdVC & MultiSetCount(m:chan, chan[m].vc = AckVC)  = 0) |
      (msg.vc = ReqVC & MultiSetCount(m:chan, chan[m].vc = AckVC)  = 0 
                    & MultiSetCount(m:chan, chan[m].vc = FwdVC)  = 0)
    ==>

      if IsMember(n, Home)
      then
        HomeReceive(msg);
        if msg_processed
        then
          MultiSetRemove(midx, chan);
        endif;
      else
        ProcReceive(msg, n);
        if msg_processed
        then
          MultiSetRemove(midx, chan);
        endif;
      endif;
    endrule;
    endalias;
    endalias;
  endchoose;  
endruleset;

----------------------------------------------------------------------
-- Startstate
----------------------------------------------------------------------
startstate

  For v:Value do
  -- home node initialization
    HomeNode.state := HI;
    undefine HomeNode.sharers;
    undefine HomeNode.owner;
    undefine HomeNode.pending_node;
    HomeNode.val := v;
  endfor;
	LastWrite := HomeNode.val;

  -- processor initialization
  for i:Proc do
    Procs[i].state := PI;
    undefine Procs[i].val;
    clear Procs[i].icount;
    clear Procs[i].acount;
  endfor;

  -- network initialization
  undefine Net;
endstartstate;


----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------
invariant "Invalid implies empty owner" --pass
  HomeNode.state = HI
    ->
      IsUndefined(HomeNode.owner);

invariant "value in memory matches value of last write, when invalid"
     HomeNode.state = HI 
    ->
			HomeNode.val = LastWrite;

invariant "values in valid state match last write"
  Forall n : Proc Do	
     Procs[n].state = PS | Procs[n].state = PM
    ->
			Procs[n].val = LastWrite --LastWrite is updated whenever a new value is created 
	end;

invariant "value is undefined while invalid" --pass
  Forall n : Proc Do	
     Procs[n].state = PI
    ->
			IsUndefined(Procs[n].val)
	end;

invariant "modified implies empty sharers list"
  HomeNode.state = HM
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;


invariant "Invalid implies empty sharer list"
  HomeNode.state = HI
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "values in memory matches value of last write, when shared or invalid"
  Forall n : Proc Do	
     HomeNode.state = HS | HomeNode.state = HI
    ->
			HomeNode.val = LastWrite
	end;

invariant "values in shared state match memory"
  Forall n : Proc Do	
     HomeNode.state = HS & Procs[n].state = PS
    ->
			HomeNode.val = Procs[n].val
	end;


