require import AllCore List SmtMap Distr IntExtra IntDiv DMap FSet.

require import ALanguage ASecretSharingScheme AProtocolLibrary AAPI ASPSemantics AMPSemantics.
require import MPCProtocolLibrary ProtocolAPI SPAPISemantics MPAPISemantics.
require import MPProtocolAPISemantics.

theory Security.

clone import Language.

clone import MultiPartyProtocolAPISemantics with
  type L1.L = L,
  type L2.L = L,
  type L3.L = L.
import ProtocolAPI.
import ProtocolLibrary.
import SecretSharingScheme.
import MultiPartyAPISemantics.

clone import SinglePartyAPISemantics with
theory Language <- L1,
type API.public_t = value_t,
type API.inputs_t = sharedValue_t,
type API.outputs_t = sharedValue_t,
type API.svar_t = svar_t,
type API.sop_t = sop_t,
type API.sideInfo_t = MPCProtocolLibrary.sideInfo_t,
type API.apiCall_data = apiCall_data,
type API.apiRes_data = apiRes_data,
type API.apiCallRes = apiCallRes,
op API.apiCall = apiCall,
op API.apiRes = apiRes,
op updRes (x: apiRes_data option) (st: ('a,'b) APIst) = (omap ApiRes x, st.`2),
op st_from_step (x: ('a,'b) ECall) = (omap ApiCall x.`1, (x.`2.`1, x.`2.`2)),
type EnvL = SemP1.EnvL,
op stepL = SemP1.stepL,
op initStateL = SemP1.initStateL,
type SinglePartySemantics.output_event_t = MultiPartySemantics.output_event_t.

module IdealFunctionality (API : SinglePartyAPISemantics.API.API_t) = {

    var st : configuration_t

    proc init(P : L) : unit = {
      st <- initial_configuration P;
      API.init();
    }
    proc step() : sideInfo_t option = {
      var r, lst, newst, cst;
      var v, xx, si;
      var vsio, asio, xxsio;

      lst <- sigma st;
      r <- None;
      cst <- callSt lst;

      if (cst = None) {
        newst <- stepL (progSt lst) (envSt lst) (resSt lst);
        if (newst <> None) {
          st <- upd_sigma (oget newst) st;
        }
      }
      else {
        match (oget cst) with
        | Call_declass a => { vsio <@ API.declass(a); 
                               if (vsio <> None) {
                                 (v, si) <- oget vsio;
                                 st <- upd_SigmaAPI (Some v) st; 
                                 r <- Some si; 
                               }
                             }
        | Call_in a => { if (ib st <> None) {
                         asio <@ API.input(a, oget (ib st)); 
                         if (asio <> None) {
                           si <- oget asio;
                           st <- upd_ib None st;
                           st <- upd_SigmaAPI None st; 
                           r <- Some si; 
                         } 
                       }
                      }
        | Call_out sv => { if (ob st = None) {
                            xxsio <@ API.output(sv);
                            if (xxsio <> None) {
                              (xx, si) <- oget xxsio;
                              st <- upd_ob (Some xx) st;
                              st <- upd_SigmaAPI None st; 
                              r <- Some si; } } }
        | Call_sop sop a pargs sargs => { asio <@ API.sop(sop, pargs, sargs, a);
                                        if (asio <> None) {
                                          si <- oget asio;
                                          st <- upd_SigmaAPI None st;
                                          r <- Some si; } }
        end;
      }
  
      return r;
    }
    proc setInput(x: inputs_t): bool = {
      var r <- false;
      if (ib st = None) {
        r <- true;
        st <- upd_ib (Some x) st;
      }
      return r;
    }
    proc getOutput(): outputs_t option = {
      var r: outputs_t option;
      r <- ob st;
      if (r <> None) {
        st <- upd_ob None st;
      }
      return r;
    }
  }.
























clone import Language as L1 with
  type public_t = value_t,
  type secret_t = sharedValue_t,
  type sop_t = sop_t,
  type inputs_t = sharedValue_t,
  type outputs_t = sharedValue_t.
clone import Language as L2 with
  type L = L,
  type public_t = value_t,
  type secret_t = sharedValue_t,
  type sop_t = sop_t,
  type inputs_t = sharedValue_t,
  type outputs_t = sharedValue_t.
clone import Language as L3 with
  type L = L,
  type public_t = value_t,
  type secret_t = sharedValue_t,
  type sop_t = sop_t,
  type inputs_t = sharedValue_t,
  type outputs_t = sharedValue_t.

clone import MultiPartyProtocolAPISemantics with
  theory L1 <- L1,
  theory L2 <- L2,
  theory L3 <- L3.


  op ProtocolLibrary.n = n,
  type ProtocolLibrary.msg_data = msg_data,
  type ProtocolLibrary.leakage_t = leakage_t,
  op ProtocolLibrary.sop_spec = sop_spec,
  op ProtocolLibrary.prot_declass = prot_declass.



print ProtocolAPI.

clone import ProtocolAPI with 
  op ProtocolLibrary.n = n,
  type ProtocolLibrary.value_t = value_t,
  type ProtocolLibrary.inputs_t = inputs_t,
  type ProtocolLibrary.inputs_t = inputs_t,
  type ProtocolLibrary.inputs_t = inputs_t,
  type ProtocolLibrary.inputs_t = inputs_t,

theory ProtocolLibrary <- ProtocolLibrary.

clone import Language as L1 with
type public_t = value_t,
type secret_t = sharedValue_t,
type sop_t = sop_t,
type inputs_t = sharedValue_t,
type outputs_t = sharedValue_t.
clone import Language as L2 with
type L = L,
type public_t = value_t,
type secret_t = sharedValue_t,
type sop_t = sop_t,
type inputs_t = sharedValue_t,
type outputs_t = sharedValue_t.
clone import Language as L3 with
type L = L,
type public_t = value_t,
type secret_t = sharedValue_t,
type sop_t = sop_t,
type inputs_t = sharedValue_t,
type outputs_t = sharedValue_t.

clone import MultiPartyAPISemantics with
theory L1 <- L1,
theory L2 <- L2,
theory L3 <- L3,
type partyId_t = partyId_t,
type API.public_t = public_t,
type API.inputs_t = sharedValue_t,
type API.outputs_t = sharedValue_t,
type API.svar_t = svar_t,
type API.sop_t = sop_t,
type API.sideInfo_t = sideInfo_t,
type API.apiCall_data = apiCall_data,
type API.apiRes_data = apiRes_data,
type API.apiCallRes = apiCallRes,
op API.apiCall = apiCall,
op API.apiRes = apiRes,
op SemP1.updRes (x: apiRes_data) (st: ('a,'b) APIst) = (Some (ApiRes x), st.`2, st.`3),
op SemP1.st_from_step (x: ('a,'b) ECall) = (omap ApiCall x.`1, x.`2, x.`3),
op SemP2.updRes (x: apiRes_data) (st: ('a,'b) APIst) = (Some (ApiRes x), st.`2, st.`3),
op SemP2.st_from_step (x: ('a,'b) ECall) = (omap ApiCall x.`1, x.`2, x.`3),
op SemP3.updRes (x: apiRes_data) (st: ('a,'b) APIst) = (Some (ApiRes x), st.`2, st.`3),
op SemP3.st_from_step (x: ('a,'b) ECall) = (omap ApiCall x.`1, x.`2, x.`3).
import MultiPartySemantics.
import API.

  (** Synchronisation points *)
  (** 
    Synchronisation points are used to check if all local
    party configurations are waiting to perform the same API
    call
  *)
  op syncPoint (api_calls : apiCall_data option * apiCall_data option * apiCall_data option): apiCall_data option =
    let (api_call1, api_call2, api_call3) = api_calls in
    if (api_call1 = api_call2 /\ api_call2 = api_call3) then api_call1 else None.

op apiCall_declass (x : apiCall_data) : svar_t option = 
with x = Call_declass v => Some v
with x = Call_in => None
with x = Call_out _ => None
with x = Call_sop _ _ _ => None.
op is_apiCall_declass (x : apiCall_data) : bool = 
with x = Call_declass v => true
with x = Call_in => false
with x = Call_out _ => false
with x = Call_sop _ _ _ => false.

op is_apiCall_in (x : apiCall_data) : bool = 
with x = Call_declass _ => false
with x = Call_in => true
with x = Call_out _ => false
with x = Call_sop _ _ _ => false.

op apiCall_out (x : apiCall_data) : svar_t option = 
with x = Call_declass _ => None
with x = Call_in => None
with x = Call_out v => Some v
with x = Call_sop _ _ _ => None.
op is_apiCall_out (x : apiCall_data) : bool = 
with x = Call_declass _ => false
with x = Call_in => false
with x = Call_out _ => true
with x = Call_sop _ _ _ => false.

op apiCall_sop (x : apiCall_data) : (sop_t * value_t list * svar_t list) option = 
with x = Call_declass _ => None
with x = Call_in => None
with x = Call_out _ => None
with x = Call_sop sop pargs sargs => None.
op is_apiCall_sop (x : apiCall_data) : bool = 
with x = Call_declass _ => false
with x = Call_in => false
with x = Call_out _ => false
with x = Call_sop _ _ _ => true.

lemma syncPoint_same_apiCall (c1 c2 c3 : apiCall_data option) :
  syncPoint (c1,c2,c3) <> None => c1 = c2 /\ c2 = c3.
proof.
rewrite /syncPoint.
simplify.
case (c1 = c2 /\ c2 = c3) => ?.
done.
done.
qed.

lemma syncPoint_exists_apiCall (c1 c2 c3 : apiCall_data option) :
  syncPoint (c1,c2,c3) <> None => c1 <> None /\ c2 <> None /\ c3 <> None.
proof.
rewrite /syncPoint.
simplify.
smt().
qed.

lemma syncPoint_same_args (c1 c2 c3 : apiCall_data option) :
  syncPoint (c1,c2,c3) <> None =>
  is_apiCall_declass (oget c1) =>
  apiCall_declass (oget c1) = apiCall_declass (oget c2) /\
  apiCall_declass (oget c2) = apiCall_declass (oget c3).
proof.  
move => ?.
have ?: c1 = c2. smt(syncPoint_same_apiCall).
have ?: c2 = c3. smt(syncPoint_same_apiCall).
have ?: c1 <> None. smt(syncPoint_exists_apiCall).
have ?: c2 <> None. smt(syncPoint_exists_apiCall).
have ?: c3 <> None. smt(syncPoint_exists_apiCall).

move => *.
by rewrite H0 H1.
qed.

print sideInfo_t.
print ProtocolLibrary.trace_t.

print trace_t.
print SemP3.sideInfo_t.
print sideInfo_t.

  module ProgSem (API: API_t) : Semantics = {

  var n: int
  var st: GlobalSt

  proc init(Prog1: L1.L, Prog2: L2.L, Prog3: L3.L): unit = {
    API.init();
    n <- API.nparties();
    st <- init_GlobalSt Prog1 Prog2 Prog3;
  }
  (* Step Public *)
  proc stepP(id: partyId_t): bool = {
    var r <- false;
    var lst1, lst2, lst3;
    var newst1, newst2, newst3;

    lst1 <- StP1 st;
    lst2 <- StP2 st;
    lst3 <- StP3 st;

    match (id) with
    | P1 => { if (SemP1.callSt lst1 = None) {
                newst1 <- SemP1.stepL (SemP1.progSt lst1) (SemP1.envSt lst1) (SemP1.resSt lst1);
                if (newst1 <> None) {
                  r <- true;
                  st <- upd_Sigma1 (oget newst1) st;
                }
              } }
    | P2 => { if (SemP2.callSt lst2 = None) {
                newst2 <- SemP2.stepL (SemP2.progSt lst2) (SemP2.envSt lst2) (SemP2.resSt lst2);
                if (newst2 <> None) {
                  r <- true;
                  st <- upd_Sigma2 (oget newst2) st;
                }
              } }
    | P3 => { if (SemP3.callSt lst3 = None) {
                newst3 <- SemP3.stepL (SemP3.progSt lst3) (SemP3.envSt lst3) (SemP3.resSt lst3);
                if (newst3 <> None) {
                  r <- true;
                  st <- upd_Sigma3 (oget newst3) st;
                }
              } }
    end;

    return r;
  }

  (* Step Secret *)
  proc stepS(): trace_t option = {
    var x, v, a, t;
    var vto, ato, xto;
    var r <- None;
    var ecall <- syncPoint (allECalls st);
    if (ecall <> None) { (* call to the API *)
      match (oget ecall) with
      | Call_declass a => { vto <@ API.declass(a);
                            if (vto <> None) {
                              (v, t) <- oget vto;
                              r <- Some t;
                              (* updates API result *)
                              st <- upd_SigmaAPI (Res_declass v) st;
                            }
                          }
      | Call_in => { if (ib st <> None) {
                         ato <@ API.input(oget (ib st));
                         if (ato <> None) {
                           (a,t) <- oget ato;
                           r <- Some t;
                           st <- upd_ib None st; (* clears buffer *)
                           st <- upd_SigmaAPI (Res_in a) st; (* resets call *)
                         }
                       }
                     }
      | Call_out a => { if (ob st = None) {
                          xto <@ API.output(a);
                          if (xto <> None) {
                            (x, t) <- oget xto;
                            r <- Some t;
                            st <- upd_ob (Some x) st; (* fills buffer *)
                            st <- upd_SigmaAPI (Res_out) st; (* resets call *)
                          }
                        }
                      }
      | Call_sop o pargs sargs => { ato <@ API.sop(o, pargs, sargs);
                                    if (ato <> None) {
                                      (a,t) <- oget ato;
                                      r <- Some t;
                                      st <- upd_SigmaAPI (Res_sop a) st; (* resets call *)
                                    }
                                  }
      end;
    }
    return r;
  }
  (*(* ideal step *)
  proc step(): sideInfo_t option = {
    var b: bool;
    var r <- None;
    if (n=1) { (* obs: only possible on the ideal world *)
      b <@ stepP(1);
      if (b) {
        r <- None;
      } else {
        r <@ stepS();
      }
    }
    return r;
  }*)
  proc setInput(x: inputs_t): bool = {
    var r <- false;
    if (ib st = None) {
      r <- true;
      st <- upd_ib (Some x) st;
    }
    return r;
  }
  proc getOutput(): outputs_t option = {
    var r: outputs_t option;
    r <- ob st;
    if (r <> None) {
      st <- upd_ob None st;
    }
    return r;
  }
}.

print SinglePartyAPISemantics.

clone import SinglePartyAPISemantics with
theory Language <- L1,
type API.public_t = value_t,
type API.inputs_t = sharedValue_t,
type API.outputs_t = sharedValue_t,
type API.svar_t = svar_t,
type API.sop_t = sop_t,
type API.sideInfo_t = MPCProtocolLibrary.sideInfo_t,
type API.apiCall_data = apiCall_data,
type API.apiRes_data = apiRes_data,
type API.apiCallRes = apiCallRes,
op API.apiCall = MultiPartyAPISemantics.API.apiCall,
op API.apiRes = MultiPartyAPISemantics.API.apiRes,
op updRes (x: apiRes_data) (st: ('a,'b) APIst) = (Some (ApiRes x), st.`2, st.`3),
op st_from_step (x: ('a,'b) ECall) = (omap ApiCall x.`1, x.`2, x.`3),
type EnvL = SemP1.EnvL,
op stepL = SemP1.stepL,
op initStateL = SemP1.initStateL,
type SinglePartySemantics.output_event_t = MultiPartySemantics.output_event_t.

import SinglePartySemantics.
print SinglePartySemantics.

print SinglePartyAPISemantics.

module SPSemantics (API : SinglePartyAPISemantics.API.API_t) = {

    var st : configuration_t

    proc init(P : L) : unit = {
      st <- initial_configuration P;
      API.init();
    }
    proc step() : sideInfo_t option = {
      var r, lst, newst, cst;
      var v, a, xx, si;
      var vsio, asio, xxsio;

      lst <- sigma st;
      r <- None;
      cst <- callSt lst;

      if (cst = None) {
        newst <- stepL (progSt lst) (envSt lst) (resSt lst);
        if (newst <> None) {
          st <- upd_sigma (oget newst) st;
        }
      }
      else {
        match (oget cst) with
        | Call_declass sv => { vsio <@ API.declass(sv); 
                               if (vsio <> None) {
                                 (v, si) <- oget vsio;
                                 st <- upd_SigmaAPI (Res_declass v) st; 
                                 r <- Some si; 
                               }
                             }
        | Call_in => { if (ib st <> None) {
                         asio <@ API.input(oget (ib st)); 
                         if (asio <> None) {
                           (a, si) <- oget asio;
                           st <- upd_ib None st;
                           st <- upd_SigmaAPI (Res_in a) st; 
                           r <- Some si; 
                         } 
                       }
                      }
        | Call_out sv => { if (ob st = None) {
                            xxsio <@ API.output(sv);
                            if (xxsio <> None) {
                              (xx, si) <- oget xxsio;
                              st <- upd_ob (Some xx) st;
                              st <- upd_SigmaAPI (Res_out) st; 
                              r <- Some si; } } }
        | Call_sop sop pargs sargs => { asio <@ API.sop(sop, pargs, sargs);
                                        if (asio <> None) {
                                          (a, si) <- oget asio;
                                          st <- upd_SigmaAPI (Res_sop a) st;
                                          r <- Some si; } }
        end;
      }
  
      return r;
    }
    proc setInput(x: inputs_t): bool = {
      var r <- false;
      if (ib st = None) {
        r <- true;
        st <- upd_ib (Some x) st;
      }
      return r;
    }
    proc getOutput(): outputs_t option = {
      var r: outputs_t option;
      r <- ob st;
      if (r <> None) {
        st <- upd_ob None st;
      }
      return r;
    }
  }.

(* [Ideal] acts as the IDEAL FUNCTIONALITY, as it consists of a single
 party that computes everything on the clear. It also specifies the leakage
 allowed in each operations.                                            *)

print MPCProtocolLibrary.sideInfo_t.
print sideInfo_t.
print API.sideInfo_t.
print MultiPartyAPISemantics.API.sideInfo_t.
print ProtocolLibrary.trace_t.

module API_Ideal (H : Handle) : SinglePartyAPISemantics.API.API_t = {
 var senv: (svar_t, value_t) fmap
 proc init(): unit = {
   senv <- empty;
 }
 proc nparties(): int = { return 1; }
 (* [declass] leaks the declassified value *)
 proc declass(a: svar_t): (value_t * sideInfo_t) option = {
   var v, r;
   r <- None;
   if (a \in senv) { v <- oget senv.[a]; r <- Some (v, Leak v); }
   return r;
 }
 (* [in] leaks the input shares from corrupted parties *)
 proc input(inp: inputs_t): (svar_t * sideInfo_t) option = {
   var a : svar_t;  
   a <@ H.create_handle(fdom senv);
   senv <- senv.[ a <- unshr(inp) ];
   return Some (a, CorruptedShares (take t inp));
 }
 (* [out] leaks the output shares from corrupted parties *)
 proc output(a: svar_t): (sharedValue_t * sideInfo_t) option = {
   var a', r;
   r <- None;
   if (a \in senv) { a' <- nshr n (oget senv.[a]); r <- Some (a', CorruptedShares (take t a')); }
   return r;
 }
 proc sop(sop: sop_t, pargs: value_t list, sargs: svar_t list)
 : (svar_t * sideInfo_t) option = {
   var y, l, a, r;
    r <- None;
    if (forall x, x \in sargs /\ x \in senv) {
      a <@ H.create_handle(fdom senv);
      (y, l) <- MPCProtocolLibrary.sop_spec sop pargs (map (fun a => (oget senv.[a])) sargs);
      senv <- senv.[ a <- y ];
      r <- Some (a, l);
    }
   return r;
 }
}.

(* REAL FUNCTIONALITY for arbritary sops:
   - [sargs] are now proper n-shared values
   - side information is the communication trace of corrupted parties *)

(* Concrete protocols. Return the communication traces for corrupted parties 
module type prot_t = {
 proc prot_declass(a: sharedValue_t): value_t * trace_t
 proc prot_in(inp: sharedValue_t): sharedValue_t * trace_t
 proc prot_out(a: sharedValue_t): sharedValue_t * trace_t
 proc prot_sop(sop: sop_t, pargs: value_t list, sargs: sharedValue_t list)
      : sharedValue_t * trace_t
}. *)


(* The REAL API *)
module API_Real (H : Handle) : API_t = {
 var senv: (svar_t, sharedValue_t) fmap
 proc init(): unit = {
   senv <- empty;
}
 proc nparties(): int = { return n; }
 proc declass(a: svar_t): (value_t * sideInfo_t) option = {
   var v, tr, r;

    r <- None;
    if (a \in senv) {
     (v, tr) <$ MPCProtocolLibrary.prot_declass(oget senv.[a]);
      r <- Some (v, Trace tr);
    }
   return r;
 }
 proc input(inp: sharedValue_t): (svar_t * sideInfo_t) option = {
   var x, tr, a;
    a <@ H.create_handle(fdom senv);
   (x, tr) <$ MPCProtocolLibrary.prot_in(inp);
   senv <- senv.[ a <- x ];
   return Some (a, Trace tr);
 }
 proc output(a: svar_t): (sharedValue_t * sideInfo_t) option = {
   var o, tr, r;
    r <- None;
    if (a \in senv) {
      (o, tr) <$ MPCProtocolLibrary.prot_out(oget (senv.[a]));
      r <- Some (o, Trace tr);
    }
   return r;
 }
 proc sop(sop: sop_t, pargs: value_t list, sargs: svar_t list)
      : (svar_t * sideInfo_t) option = {
   var r, tr, a, y;
    r <- None;
    if (forall x, x \in sargs /\ x \in senv) {
      a <@ H.create_handle(fdom senv);
      (y, tr) <$ MPCProtocolLibrary.prot_sop sop pargs (map (fun a => oget senv.[a]) sargs);
      senv <- senv.[ a <- y ];
      r <- Some (a, Trace tr);
    }
   return r;
 }
}.


module type IdealInterface = {
  proc init(P : L) : unit
  proc step(): sideInfo_t option
}.

(*module type SimEnvInterface = {
  proc activate(): trace_t
}.*)

module type SimInterface (Sem: IdealInterface) = {
  include AdvSemInterface
}.

module API_Simulator (H : Handle) (ISem : IdealInterface): API_t = {
 var senv: (svar_t, sharedValue_t) fmap
 proc init(): unit = {
   senv <- empty;
}
 proc nparties(): int = { return n; }
 proc declass(a: svar_t): (value_t * sideInfo_t) option = {
   var v, t, ir, r;
    r <- None;
    if (a \in senv) {
      ir <@ ISem.step();
      (v, t) <$ MPCProtocolLibrary.sim_declass (oget (senv.[a])) (leakedValue (oget ir)); 
      r <- Some (v, Trace t);
    }
   return r;
 }

 proc input(inp: sharedValue_t): (svar_t * sideInfo_t) option = {
   var x, tr, a, r;
    r <@ ISem.step();
    a <@ H.create_handle(fdom senv);
   (x, tr) <$ MPCProtocolLibrary.sim_in(corruptedShares (oget r));
   senv <- senv.[ a <- x ];
   return Some (a, Trace tr);
 }

 proc output(a: svar_t): (sharedValue_t * sideInfo_t) option = {
   var o, yy, tr, r;
    r <- None;
    if (a \in senv) {
      o <@ ISem.step();
      yy <- corruptedShares (oget o);
      tr <$ MPCProtocolLibrary.sim_out(oget (senv.[a])) yy; 
      r <- Some (yy, Trace tr);
    }
   return r;
 }

 proc sop(sop: sop_t, pargs: value_t list, sargs: svar_t list)
      : (svar_t * sideInfo_t) option = {
   var y, tr, a, l, r;
    r <- None;
    if (forall x, x \in sargs /\ x \in senv) {
      l <@ ISem.step();
      a <@ H.create_handle(fdom senv);
      (y, tr) <$ MPCProtocolLibrary.sim_sop sop pargs ((map (fun a => oget senv.[a]) sargs)) (oget l);
      senv <- senv.[ a <- y ];
      r <- Some (a, Trace tr);
    }
   return r;
 }
}.

section Security.

op create_handle (hdls : svar_t fset) : svar_t distr.
axiom create_handle_ll hdls : is_lossless (create_handle hdls).
axiom create_handle_inj vs vs' :
  vs = vs' => create_handle vs = create_handle vs'.
axiom create_handle_fresh vs v :
  v \in create_handle vs =>
  !(v \in vs).

module H : Handle = {
  proc create_handle(hdls : svar_t fset) : svar_t = {
    var h;
    h <$ create_handle hdls;
    return h;
  }
}.


local module IdealSem = SPSemantics(API_Ideal(H)).
local module RealSem = ProgSem(API_Real(H)).
(*local module SimSem = SimulatorSemantics.ProgSem(Simulator(H,IdealSem)).*)

local module Simulator : MultiPartySemantics.Semantics = {
  (* Simulator runs a local copy of all parties... *)
  (*module RSem = RealSem
  module ISem = IdealSem*)

  (*include SimSem [-init, stepP, stepS, setInput, getOutput]*)
  include RealSem[-init, stepP, stepS, setInput, getOutput]

  (* secret state from corrupted parties *)
  var senv : (svar_t, sharedValue_t) fmap

  proc init(P1:L1.L, P2:L2.L, P3:L3.L): unit = {
    RealSem.init(P1,P2,P3);
    IdealSem.init(P1);
    (*SimSem.init(P);*)
    API_Simulator(H,IdealSem).init();
  }
  (* [stepP] rely on the local [RealSem] module to .
     It also keeps the ISem synchronized with party 1 *)
  proc stepP(id: partyId_t): bool = {
    var r, x;
    r <- RealSem.stepP(id);
    if (id = P1 /\ r) { x <@ IdealSem.step(); }
    return r;
  }
  (* Step Secret *)
  proc stepS(): sideInfo_t option = {
    var v, x, t, a;
    var vto, ato, xto;
    var r <- None;
    var ecall <- syncPoint (allECalls RealSem.st);
    if (ecall <> None) { (* call to the API *)
      (* call the Ideal world [step] method *)
(*      r <@ ISem.step();
      (* now, call the atomic simulators and keep the emulated parties' state synchronized *)
      if (r <> None) {*)
        match (oget ecall) with
        | Call_declass a =>
          { vto <@ API_Simulator(H,IdealSem).declass(a); 
            if (vto <> None) {
              (v, t) <- oget vto;
              r <- Some t;
              (* updates API result *)
              RealSem.st <- upd_SigmaAPI (Res_declass v) RealSem.st;
          } }
        | Call_in =>
          { if (ib RealSem.st <> None) {
              ato <@ API_Simulator(H,IdealSem).input(oget (ib RealSem.st));
              if (ato <> None) {
                (a,t) <- oget ato;
                r <- Some t;
                RealSem.st <- upd_ib None RealSem.st;
                RealSem.st <- upd_SigmaAPI (Res_in a) RealSem.st; (* resets call *)
            } } }
        | Call_out a =>
          { if (ob RealSem.st = None) {
              xto <@ API_Simulator(H,IdealSem).output(a);
              if (xto <> None) {
                (x,t) <- oget xto;
                r <- Some t;
                RealSem.st <- upd_ob (Some x) RealSem.st;
                RealSem.st <- upd_SigmaAPI (Res_out) RealSem.st; (* resets call *)
          } } }
        | Call_sop o pargs sargs =>
          { ato <@ API_Simulator(H,IdealSem).sop(o, pargs, sargs); 
            if (ato <> None) {
              (a,t) <- oget ato;
              r <- Some t;
              RealSem.st <- upd_SigmaAPI (Res_sop a) RealSem.st; (* resets call *)  
            } }
        end;
      }
    
    return r;
  }
  proc setInput(x: sharedValue_t): bool = {
    var r <- false;
    r <@ RealSem.setInput(x);
    if (r) {
      r <@ IdealSem.setInput(x);
    }
    return r;
  }
  proc getOutput(): sharedValue_t option = {
    var r: sharedValue_t option;
    r <@ RealSem.getOutput();
    if (r <> None) {
      IdealSem.getOutput();
    }
    return r;
  }
}.

local module RealGame (Z: Environment) (A: MultiPartySemantics.Adversary) = MultiPartySemantics.Eval(RealSem,Z,A). 

local module IdealGame (Z: Environment) (A: MultiPartySemantics.Adversary) = MultiPartySemantics.Eval(Simulator,Z, A).

declare module Z : Environment {ProgSem,API_Ideal,Simulator,H,API_Real,Simulator}.
declare module A : MultiPartySemantics.Adversary {ProgSem,Z,Simulator}.

lemma fdom_map_eq (m : ('a, 'b) fmap) (m' : ('a, 'c) fmap) :
  (forall x, x \in m <=> x \in m') =>
  fdom m = fdom m'.
proof.
move => *.
rewrite !fdomE.
rewrite /dom.
congr.
congr.
rewrite fun_ext /(==) => y.
smt().
qed.

(*clone import DMapSampling as DMapDeclass with
type t1 = MPCProtocolLibrary.value_t * MPCProtocolLibrary.trace_t,
type t2 = MPCProtocolLibrary.value_t * MPCProtocolLibrary.trace_t.

clone import DMapSampling as DMapInput with
type t1 = sharedValue_t * MPCProtocolLibrary.trace_t,
type t2 = sharedValue_t * MPCProtocolLibrary.trace_t.*)

local equiv Security:
 RealGame(Z, A).eval ~ IdealGame(Z, A).eval : ={P1, P2, P3, glob Z, glob A, glob H} ==> ={res}.
proof.
proc.
inline*.
sp.


call (_ : ={glob A, glob ProgSem} /\
  (forall v, v \in API_Real.senv{1} <=> v \in API_Ideal.senv{2}) /\
  (forall v, v \in API_Real.senv{1} <=> v \in API_Simulator.senv{2}) /\
  (forall v, v \in API_Real.senv{1} => API_Ideal.senv{2}.[v] = Some (unshr (oget API_Real.senv{1}.[v]))) /\
  (forall v, v \in API_Real.senv{1} => oget API_Simulator.senv{2}.[v] = take t (oget API_Real.senv{1}.[v])) /\
  ProgSem.n{1} = Security.n /\
  ProgSem.st{1}.`StP1 = SPSemantics.st{2}.`sigma /\
  ProgSem.st{1}.`ib = SPSemantics.st{2}.`ib /\
  ProgSem.st{1}.`ob = SPSemantics.st{2}.`ob
  ).

proc; inline*.
sp 2 4.
if.
done.
rcondt{2} 4.
move => &m.
by wp.
rcondt{2} 6.
move => &m.
wp; skip; progress.
rewrite -H4.
done.
by wp.
rcondf{2} 2.
move => &m.
by wp.
by wp.

proc; inline*.
sp 1 1.
if.
done.
rcondt{2} 3.
move => &m.
by wp.
rcondt{2} 4.
move => &m.
wp; skip; progress.
rewrite -H5.
done.
by wp.
rcondf{2} 2.
move => &m.
by wp.
by wp.

proc; inline*.

call (_ : ={glob ProgSem} /\
  (forall v, v \in API_Real.senv{1} <=> v \in API_Ideal.senv{2}) /\
  (forall v, v \in API_Real.senv{1} <=> v \in API_Simulator.senv{2}) /\
  (forall v, v \in API_Real.senv{1} => API_Ideal.senv{2}.[v] = Some (unshr (oget API_Real.senv{1}.[v]))) /\
  (forall v, v \in API_Real.senv{1} => oget API_Simulator.senv{2}.[v] = take t (oget API_Real.senv{1}.[v])) /\
  ProgSem.n{1} = Security.n /\
  ProgSem.st{1}.`StP1 = SPSemantics.st{2}.`sigma /\
  ProgSem.st{1}.`ib = SPSemantics.st{2}.`ib /\
  ProgSem.st{1}.`ob = SPSemantics.st{2}.`ob
  ).

proc; inline*.

sp 4 5.
match.
done.
done.
done.
if.
done.
sp 1 1.
if.
done.
sp 2 3.
if{2}; last first.
by skip.
rcondt{2} 4.
move => &m.
wp; skip; progress.
rewrite -H3.
rewrite H6.
done.
rcondt{2} 5.
move => &m.
wp; skip; progress.
rewrite -H3.
rewrite H7.
done.  
wp; skip; progress.

smt().
smt().
smt().
smt().
smt().

rcondf{2} 2.
move => &m.
by wp; skip.
by wp; skip.

rcondf{2} 2.
move => &m.
by wp; skip.
by wp; skip.

if.
done.
sp 1 1.
if.
done.
sp 2 3.
if{2}; last first.
by wp.
rcondt{2} 4.
move => &m.
by wp; skip.
rcondt{2} 5.
move => &m.
by wp; skip.
by wp; skip.

rcondf{2} 2.
move => &m.
by wp; skip.
by wp; skip.

rcondf{2} 2.
move => &m.
by wp; skip.
by wp; skip.

if.
done.
sp 1 1.
if.
done.
sp 2 3.
if{2}; last first.
by wp; skip.
rcondt{2} 4.
move => &m.
by wp; skip.
rcondt{2} 5.
move => &m.
by wp; skip.
by wp; skip.

rcondf{2} 2.
move => &m.
by wp; skip.
by wp; skip.

rcondf{2} 2.
move => &m.
by wp; skip.
by wp; skip.

proc; inline*.
sp 2 2.
if; last first.
by skip.
done.
match => //=.
move => a a'.
sp 2 2.
if.
move => &1 &2 => /#.
rcondf{2} 4. 
move => &m.
by wp; skip; smt(syncPoint_exists_apiCall).

sp 0 3.
match{2}.
move => sv.
rcondt{2} 3.
move => &m.
by wp; skip => /#.
rcondt{2} 6.
move => &m.
by wp; skip.
rcondt{2} 13.
move => &m.
by wp; rnd; wp; skip.
rcondt{1} 4.
move => &m.
by wp; rnd; skip.

wp; rnd; wp; skip; progress.
rewrite (declass_security (oget API_Real.senv{1}.[a0{1}]) (leakedValue (Leak (oget API_Ideal.senv{2}.[sv]))) (oget API_Simulator.senv{2}.[a0{2}])).
smt().
smt().
done.

rewrite -(declass_security (oget API_Real.senv{1}.[a0{1}]) (leakedValue (Leak (oget API_Ideal.senv{2}.[sv]))) (oget API_Simulator.senv{2}.[a0{2}])).
smt().
smt().
done.

smt(declass_correctness).
smt().
smt().
smt().
smt().

exfalso => /#.
move => sv; exfalso => /#.
move => *; exfalso => /#.
by wp; skip.

(* INPUT *)
if.
progress.
rcondt{1} 8.
move => &m.
auto; skip; progress.
rcondf{2} 5.
move => &m.
wp; skip; progress.
smt().

sp 0 4.
match{2}.
move => sv.
exfalso => /#.
rcondt{2} 1.
move => &m.
wp; skip; progress.
smt().
rcondt{2} 7.
move => &m.
auto; skip; progress.
rcondt{2} 18.
auto; skip; progress.




wp 3 11.
sp 0 6.

swap{2} 1 4.
seq 0 1 : (#[1:8,9:]pre /\ r4{2} = Some si{2}).
by wp; skip.
sp.
wp 2 1.

(* 10 *)

transitivity{1} 
{
(v0, tr) <@ DMapDeclass.S.map(MPCProtocolLibrary.prot_declass (oget Real.senv.[a0]), declass_projection);
}
  ((a0{2} = a0{1} /\
    ecall{1} = ecall{2} /\
    oget ecall{2} = Call_declass a' /\
    (
     ecall{1} = syncPoint (allECalls ProgSem.st{1}) /\
     ={ProgSem.st, ProgSem.n, glob Real} /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        oget Simulator.senv{2}.[v9] =
        take Security.t (oget Real.senv{1}.[v9])) /\
     ProgSem.n{1} = Security.n /\
     ProgSem.st{1}.`StP1 = SPSemantics.st{2}.`sigma /\
     ProgSem.st{1}.`ib = SPSemantics.st{2}.`ib /\
     ProgSem.st{1}.`ob = SPSemantics.st{2}.`ob) /\
    ecall{1} <> None) /\
   (a0{1} \in Real.senv{1})
 ==> ={v0,tr} /\ ={glob ProgSem, glob Real}

/\ let st_R = upd_SigmaAPI (Res_declass (oget Ideal.senv{2}.[a0{1}])) SPSemantics.st{2} in
  let tpl = oget (Some (v0{2}, Trace tr{2})) in
  let tpl0 = oget (Some (v0{1}, Trace tr{1})) in
  let st_L = upd_SigmaAPI (Res_declass tpl0.`1) ProgSem.st{1} in
  Some tpl0.`2 = Some tpl.`2 /\
  (st_L = upd_SigmaAPI (Res_declass tpl.`1) RealSem.st{2} /\ ={ProgSem.n}) /\
  (forall (v9 : svar_t), v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
  (forall (v9 : svar_t),
     v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
  (forall (v9 : svar_t),
     v9 \in Real.senv{1} =>
     Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
  (forall (v9 : svar_t),
     v9 \in Real.senv{1} =>
     oget Simulator.senv{2}.[v9] =
     take Security.t (oget Real.senv{1}.[v9])) /\
  ProgSem.n{1} = Security.n /\
  st_L.`StP1 = st_R.`sigma /\ st_L.`ib = st_R.`ib /\ st_L.`ob = st_R.`ob)

(ir{2} = r4{2} /\
  (a8{2} = sv /\
   v5{2} = oget Ideal.senv{2}.[a8{2}] /\
   r8{2} = Some (v5{2}, Leak v5{2}) /\
   vsio{2} = r8{2} /\
   (v1{2}, si{2}) = oget vsio{2} /\
   oget cst{2} = Call_declass sv /\
   lst{2} = SPSemantics.st{2}.`sigma /\
   cst{2} = callSt lst{2} /\
   (a0{2} = a' /\
    r0{2} = None /\
    a0{1} = a /\
    r0{1} = None /\
    oget ecall{1} = Call_declass a /\
    oget ecall{2} = Call_declass a' /\
    (r{2} = None /\
     ecall{2} = syncPoint (allECalls ProgSem.st{2}) /\
     r{1} = None /\
     ecall{1} = syncPoint (allECalls ProgSem.st{1}) /\
     ={ProgSem.st, ProgSem.n} /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        oget Simulator.senv{2}.[v9] =
        take Security.t (oget Real.senv{1}.[v9])) /\
     ProgSem.n{1} = Security.n /\
     ProgSem.st{1}.`StP1 = SPSemantics.st{2}.`sigma /\
     ProgSem.st{1}.`ib = SPSemantics.st{2}.`ib /\
     ProgSem.st{1}.`ob = SPSemantics.st{2}.`ob) /\
    ecall{1} <> None) /\
   (a0{1} \in Real.senv{1})) /\
  r4{2} = Some si{2}
 ==> ={v0} /\ tr{1} = t0{2} /\ let st_R = upd_SigmaAPI (Res_declass v1{2}) SPSemantics.st{2} in
  let tpl = oget (Some (v0{2}, Trace t0{2})) in
  let tpl0 = oget (Some (v0{1}, Trace tr{1})) in
  let st_L = upd_SigmaAPI (Res_declass tpl0.`1) ProgSem.st{1} in
  Some tpl0.`2 = Some tpl.`2 /\
  (st_L = upd_SigmaAPI (Res_declass tpl.`1) RealSem.st{2} /\ ={ProgSem.n}) /\
  (forall (v9 : svar_t), v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
  (forall (v9 : svar_t),
     v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
  (forall (v9 : svar_t),
     v9 \in Real.senv{1} =>
     Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
  (forall (v9 : svar_t),
     v9 \in Real.senv{1} =>
     oget Simulator.senv{2}.[v9] =
     take Security.t (oget Real.senv{1}.[v9])) /\
  ProgSem.n{1} = Security.n /\
  st_L.`StP1 = st_R.`sigma /\ st_L.`ib = st_R.`ib /\ st_L.`ob = st_R.`ob).
move => *.
exists (Ideal.senv{2}) (Real.senv{1}) (Simulator.senv{2}) n (ProgSem.st{1}) (SPSemantics.st{2}) (a0{1}) (ecall{1}) None None.
smt().
progress.

inline*.
alias{1} 1.
wp; rnd; wp; skip; progress.
smt().
smt().
smt().
smt().
smt(declass_correctness declass_projection_correctness declass_projection_supp declass_projection_exists declass_security declass_security_mu1 declass_projection_sim_support declass_sim_projection_support).
smt().
smt().
smt().
smt().

transitivity{1} 
{
(v0, tr) <@ DMapDeclass.S.sample(MPCProtocolLibrary.prot_declass (oget Real.senv.[a0]), declass_projection);
}
  ((a0{2} = a0{1} /\ 
    ecall{1} = ecall{2} /\
    oget ecall{2} = Call_declass a' /\
    (
     ecall{1} = syncPoint (allECalls ProgSem.st{1}) /\
     ={ProgSem.st, ProgSem.n, glob Real} /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        oget Simulator.senv{2}.[v9] =
        take Security.t (oget Real.senv{1}.[v9])) /\
     ProgSem.n{1} = Security.n /\
     ProgSem.st{1}.`StP1 = SPSemantics.st{2}.`sigma /\
     ProgSem.st{1}.`ib = SPSemantics.st{2}.`ib /\
     ProgSem.st{1}.`ob = SPSemantics.st{2}.`ob) /\
    ecall{1} <> None) /\
   (a0{1} \in Real.senv{1})
 ==> ={v0,tr} /\ ={glob ProgSem, glob Real}

/\ ={v0} /\
  tr{1} = tr{2} /\
  let st_R = upd_SigmaAPI (Res_declass v0{2}) SPSemantics.st{2} in
  let tpl = oget (Some (v0{2}, Trace tr{2})) in
  let tpl0 = oget (Some (v0{1}, Trace tr{1})) in
  let st_L = upd_SigmaAPI (Res_declass tpl0.`1) ProgSem.st{1} in
  Some tpl0.`2 = Some tpl.`2 /\
  (st_L = upd_SigmaAPI (Res_declass tpl.`1) RealSem.st{2} /\ ={ProgSem.n}) /\
  (forall (v9 : svar_t), v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
  (forall (v9 : svar_t),
     v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
  (forall (v9 : svar_t),
     v9 \in Real.senv{1} =>
     Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
  (forall (v9 : svar_t),
     v9 \in Real.senv{1} =>
     oget Simulator.senv{2}.[v9] =
     take Security.t (oget Real.senv{1}.[v9])) /\
  ProgSem.n{1} = Security.n /\
  st_L.`StP1 = st_R.`sigma /\ st_L.`ib = st_R.`ib /\ st_L.`ob = st_R.`ob)

(ir{2} = r4{2} /\
  (a8{2} = sv /\
   v5{2} = oget Ideal.senv{2}.[a8{2}] /\
   r8{2} = Some (v5{2}, Leak v5{2}) /\
   vsio{2} = r8{2} /\
   (v1{2}, si{2}) = oget vsio{2} /\
   oget cst{2} = Call_declass sv /\
   lst{2} = SPSemantics.st{2}.`sigma /\
   cst{2} = callSt lst{2} /\
   (a0{2} = a' /\
    r0{2} = None /\
    a0{1} = a /\
    r0{1} = None /\
    oget ecall{1} = Call_declass a /\
    oget ecall{2} = Call_declass a' /\
    (r{2} = None /\
     ecall{2} = syncPoint (allECalls ProgSem.st{2}) /\
     r{1} = None /\
     ecall{1} = syncPoint (allECalls ProgSem.st{1}) /\
     ={ProgSem.st, ProgSem.n} /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        oget Simulator.senv{2}.[v9] =
        take Security.t (oget Real.senv{1}.[v9])) /\
     ProgSem.n{1} = Security.n /\
     ProgSem.st{1}.`StP1 = SPSemantics.st{2}.`sigma /\
     ProgSem.st{1}.`ib = SPSemantics.st{2}.`ib /\
     ProgSem.st{1}.`ob = SPSemantics.st{2}.`ob) /\
    ecall{1} <> None) /\
   (a0{1} \in Real.senv{1})) /\
  r4{2} = Some si{2}
 ==> ={v0} /\ tr{1} = t0{2} /\ ={v0} /\
  tr{1} = t0{2} /\
  let st_R = upd_SigmaAPI (Res_declass v1{2}) SPSemantics.st{2} in
  let tpl = oget (Some (v0{2}, Trace t0{2})) in
  let tpl0 = oget (Some (v0{1}, Trace tr{1})) in
  let st_L = upd_SigmaAPI (Res_declass tpl0.`1) ProgSem.st{1} in
  Some tpl0.`2 = Some tpl.`2 /\
  (st_L = upd_SigmaAPI (Res_declass tpl.`1) RealSem.st{2} /\ ={ProgSem.n}) /\
  (forall (v9 : svar_t), v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
  (forall (v9 : svar_t),
     v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
  (forall (v9 : svar_t),
     v9 \in Real.senv{1} =>
     Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
  (forall (v9 : svar_t),
     v9 \in Real.senv{1} =>
     oget Simulator.senv{2}.[v9] =
     take Security.t (oget Real.senv{1}.[v9])) /\
  ProgSem.n{1} = Security.n /\
  st_L.`StP1 = st_R.`sigma /\ st_L.`ib = st_R.`ib /\ st_L.`ob = st_R.`ob).
move => *.
exists (Ideal.senv{2}) (Real.senv{1}) (Simulator.senv{2}) n (ProgSem.st{1}) (SPSemantics.st{2}) (a0{1}) (ecall{1}) None None.
smt().
progress.

symmetry.
call DMapDeclass.sample.
skip; progress.
smt().
smt().
smt().
smt().

(** 10 *)

inline*.
alias{2} 1.
wp; rnd; wp; skip; progress.
smt(declass_correctness declass_projection_correctness declass_projection_supp declass_projection_exists declass_security declass_security_mu1 declass_projection_sim_support declass_sim_projection_support syncPoint_same_apiCall).
smt(declass_correctness declass_projection_correctness declass_projection_supp declass_projection_exists declass_security declass_security_mu1 declass_projection_sim_support declass_sim_projection_support syncPoint_same_apiCall).
smt(declass_correctness declass_projection_correctness declass_projection_supp declass_projection_exists declass_security declass_security_mu1 declass_projection_sim_support declass_sim_projection_support syncPoint_same_apiCall).

smt().
smt().
smt().
smt().

exfalso => /#.
progress.
exfalso => /#.
progress.
exfalso => /#.

sp 1 1.
if.
done.
exfalso => /#.
by skip.

if.
progress.
rcondt{1} 9.
move => &m.
auto; skip; progress.
rcondf{2} 5.
move => &m.
wp; skip; progress.
smt().

sp 0 4.
match{2}.
move => sv.
exfalso => /#.
rcondt{2} 1.
move => &m.
wp; skip; progress.
smt().
rcondt{2} 7.
move => &m.
auto; skip; progress.
rcondt{2} 18.
auto; skip; progress.
wp 6 15.
sp.
seq 1 1 : (#pre /\ h{1} \in create_handle (fdom Real.senv{1}) /\ h3{2} \in  create_handle (fdom Ideal.senv{2}) /\ h{1} = h3{2}).
rnd{1}. rnd{2}.
skip; progress.
apply create_handle_ll.
apply create_handle_ll.
smt(fdom_map_eq create_handle_inj).
sp 1 1.

(* transitivity *)
transitivity{1} 
{
(x0, tr0) <@ DMapInput.S.map(MPCProtocolLibrary.prot_in (oget ProgSem.st.`ib), in_projection);
}
( ={glob ProgSem, glob Real, a1} /\
  a1{1} = h{1} /\
  (
   inp{1} = oget ProgSem.st{1}.`ib /\
   hdls{1} = fdom Real.senv{1} /\
   inp{2} = oget RealSem.st{2}.`ib /\
   (oget ecall{1} = Call_in /\
    oget ecall{2} = Call_in /\
    (r{2} = None /\
     ecall{2} = syncPoint (allECalls ProgSem.st{2}) /\
     r{1} = None /\
     ecall{1} = syncPoint (allECalls ProgSem.st{1}) /\
     ={ProgSem.st, ProgSem.n} /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        oget Simulator.senv{2}.[v9] =
        take Security.t (oget Real.senv{1}.[v9])) /\
     ProgSem.n{1} = Security.n /\
     ProgSem.st{1}.`StP1 = SPSemantics.st{2}.`sigma /\
     ProgSem.st{1}.`ib = SPSemantics.st{2}.`ib /\
     ProgSem.st{1}.`ob = SPSemantics.st{2}.`ob) /\
    ecall{1} <> None) /\
   ProgSem.st{1}.`ib <> None) /\
  (h{1} \in create_handle (fdom Real.senv{1})) 
==>
={x0,a1} /\ tr0{1} = tr0{2} /\ ={glob ProgSem, glob Real})

(a13{2} = h3{2} /\
  a1{1} = h{1} /\
  (inp1{2} = oget SPSemantics.st{2}.`ib /\
   hdls3{2} = fdom Ideal.senv{2} /\
   inp{1} = oget ProgSem.st{1}.`ib /\
   hdls{1} = fdom Real.senv{1} /\
   oget cst0{2} = Call_in /\
   inp{2} = oget RealSem.st{2}.`ib /\
   lst0{2} = SPSemantics.st{2}.`sigma /\
   r5{2} = None /\
   cst0{2} = callSt lst0{2} /\
   (oget ecall{1} = Call_in /\
    oget ecall{2} = Call_in /\
    (r{2} = None /\
     ecall{2} = syncPoint (allECalls ProgSem.st{2}) /\
     r{1} = None /\
     ecall{1} = syncPoint (allECalls ProgSem.st{1}) /\
     ={ProgSem.st, ProgSem.n} /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        oget Simulator.senv{2}.[v9] =
        take Security.t (oget Real.senv{1}.[v9])) /\
     ProgSem.n{1} = Security.n /\
     ProgSem.st{1}.`StP1 = SPSemantics.st{2}.`sigma /\
     ProgSem.st{1}.`ib = SPSemantics.st{2}.`ib /\
     ProgSem.st{1}.`ob = SPSemantics.st{2}.`ob) /\
    ecall{1} <> None) /\
   ProgSem.st{1}.`ib <> None) /\
  (h{1} \in create_handle (fdom Real.senv{1})) /\
  (h3{2} \in create_handle (fdom Ideal.senv{2})) /\ h{1} = h3{2}
==> take t x0{1} = x0{2} /\ tr0{1} = tr{2} /\
let senv_R = Simulator.senv{2}.[a1{2} <- x0{2}] in
  let tpl = oget (Some (a1{2}, Trace tr{2})) in
  let senv_L = Real.senv{1}.[a1{1} <- x0{1}] in
  let tpl0 = oget (Some (a1{1}, Trace tr0{1})) in
  let st_L = upd_SigmaAPI (Res_in tpl0.`1) (upd_ib None ProgSem.st{1}) in
  Some tpl0.`2 = Some tpl.`2 /\
  (st_L = upd_SigmaAPI (Res_in tpl.`1) (upd_ib None RealSem.st{2}) /\
   ={ProgSem.n}) /\
  (forall (v9 : svar_t), v9 \in senv_L <=> v9 \in Ideal.senv{2}) /\
  (forall (v9 : svar_t), v9 \in senv_L <=> v9 \in senv_R) /\
  (forall (v9 : svar_t),
     v9 \in senv_L =>
     Ideal.senv{2}.[v9] = Some (unshr (oget senv_L.[v9]))) /\
  (forall (v9 : svar_t),
     v9 \in senv_L => oget senv_R.[v9] = take Security.t (oget senv_L.[v9])) /\
  ProgSem.n{1} = Security.n /\
  st_L.`StP1 = SPSemantics.st{2}.`sigma /\
  st_L.`ib = SPSemantics.st{2}.`ib /\ st_L.`ob = SPSemantics.st{2}.`ob).

progress.
exists (Ideal.senv{2}) (Real.senv{1}) (Simulator.senv{2}) n (ProgSem.st{2}) (SPSemantics.st{2}) (h3{2}) (syncPoint (allECalls ProgSem.st{2})) (h3{2}) (fdom Real.senv{1}) (oget ProgSem.st{2}.`ib) None.
done.
progress.

inline*.
alias{1} 1.
wp.
rnd.
wp; skip; progress.
smt().
smt().

transitivity{1} 
{
(x0, tr0) <@ DMapInput.S.sample(MPCProtocolLibrary.prot_in (oget ProgSem.st.`ib), in_projection);
}
( ={glob ProgSem, glob Real, a1} /\
  a1{1} = h{1} /\
  (
   inp{1} = oget ProgSem.st{1}.`ib /\
   hdls{1} = fdom Real.senv{1} /\
   inp{2} = oget RealSem.st{2}.`ib /\
   (oget ecall{1} = Call_in /\
    oget ecall{2} = Call_in /\
    (r{2} = None /\
     ecall{2} = syncPoint (allECalls ProgSem.st{2}) /\
     r{1} = None /\
     ecall{1} = syncPoint (allECalls ProgSem.st{1}) /\
     ={ProgSem.st, ProgSem.n} /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        oget Simulator.senv{2}.[v9] =
        take Security.t (oget Real.senv{1}.[v9])) /\
     ProgSem.n{1} = Security.n /\
     ProgSem.st{1}.`StP1 = SPSemantics.st{2}.`sigma /\
     ProgSem.st{1}.`ib = SPSemantics.st{2}.`ib /\
     ProgSem.st{1}.`ob = SPSemantics.st{2}.`ob) /\
    ecall{1} <> None) /\
   ProgSem.st{1}.`ib <> None) /\
  (h{1} \in create_handle (fdom Real.senv{1})) 
==>
={x0,a1,tr0} /\ ={glob ProgSem, glob Real})

(a13{2} = h3{2} /\
  a1{1} = h{1} /\
  (inp1{2} = oget SPSemantics.st{2}.`ib /\
   hdls3{2} = fdom Ideal.senv{2} /\
   inp{1} = oget ProgSem.st{1}.`ib /\
   hdls{1} = fdom Real.senv{1} /\
   oget cst0{2} = Call_in /\
   inp{2} = oget RealSem.st{2}.`ib /\
   lst0{2} = SPSemantics.st{2}.`sigma /\
   r5{2} = None /\
   cst0{2} = callSt lst0{2} /\
   (oget ecall{1} = Call_in /\
    oget ecall{2} = Call_in /\
    (r{2} = None /\
     ecall{2} = syncPoint (allECalls ProgSem.st{2}) /\
     r{1} = None /\
     ecall{1} = syncPoint (allECalls ProgSem.st{1}) /\
     ={ProgSem.st, ProgSem.n} /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        oget Simulator.senv{2}.[v9] =
        take Security.t (oget Real.senv{1}.[v9])) /\
     ProgSem.n{1} = Security.n /\
     ProgSem.st{1}.`StP1 = SPSemantics.st{2}.`sigma /\
     ProgSem.st{1}.`ib = SPSemantics.st{2}.`ib /\
     ProgSem.st{1}.`ob = SPSemantics.st{2}.`ob) /\
    ecall{1} <> None) /\
   ProgSem.st{1}.`ib <> None) /\
  (h{1} \in create_handle (fdom Real.senv{1})) /\
  (h3{2} \in create_handle (fdom Ideal.senv{2})) /\ h{1} = h3{2}
==> take Security.t x0{1} = x0{2} /\
  tr0{1} = tr{2} /\
  let senv_R = Simulator.senv{2}.[a1{2} <- x0{2}] in
  let tpl = oget (Some (a1{2}, Trace tr{2})) in
  let senv_L = Real.senv{1}.[a1{1} <- x0{1}] in
  let tpl0 = oget (Some (a1{1}, Trace tr0{1})) in
  let st_L = upd_SigmaAPI (Res_in tpl0.`1) (upd_ib None ProgSem.st{1}) in
  Some tpl0.`2 = Some tpl.`2 /\
  (st_L = upd_SigmaAPI (Res_in tpl.`1) (upd_ib None RealSem.st{2}) /\
   ={ProgSem.n}) /\
  (forall (v9 : svar_t), v9 \in senv_L <=> v9 \in Ideal.senv{2}) /\
  (forall (v9 : svar_t), v9 \in senv_L <=> v9 \in senv_R) /\
  (forall (v9 : svar_t),
     v9 \in senv_L =>
     Ideal.senv{2}.[v9] = Some (unshr (oget senv_L.[v9]))) /\
  (forall (v9 : svar_t),
     v9 \in senv_L => oget senv_R.[v9] = take Security.t (oget senv_L.[v9])) /\
  ProgSem.n{1} = Security.n /\
  st_L.`StP1 = SPSemantics.st{2}.`sigma /\
  st_L.`ib = SPSemantics.st{2}.`ib /\ st_L.`ob = SPSemantics.st{2}.`ob).

progress.
exists (Ideal.senv{2}) (Real.senv{1}) (Simulator.senv{2}) n (ProgSem.st{2}) (SPSemantics.st{2}) (h3{2}) (syncPoint (allECalls ProgSem.st{2})) (h3{2}) (fdom Real.senv{1}) (oget ProgSem.st{2}.`ib) None.
done.
progress.

symmetry.
call (DMapInput.sample).
skip; progress.

(***************************************************************************)

inline*.
wp.
rnd{1}. rnd{2}. (* FIX ME? *)
wp.
rnd{2}.
wp; skip; progress.
apply create_handle_ll.
apply sim_in_ll.
rewrite dmap_ll.
apply prot_in_ll.
smt(fdom_map_eq create_handle_inj mem_set get_setE in_correctness in_security supp_dmap).
smt(fdom_map_eq create_handle_inj mem_set get_setE in_correctness in_security supp_dmap).
smt(fdom_map_eq create_handle_inj mem_set get_setE in_correctness in_security supp_dmap).

smt(fdom_map_eq create_handle_inj).
smt(fdom_map_eq create_handle_inj mem_set).
smt(fdom_map_eq create_handle_inj mem_set).
smt(fdom_map_eq create_handle_inj mem_set).
smt(fdom_map_eq create_handle_inj mem_set).
smt(fdom_map_eq create_handle_inj mem_set get_setE in_correctness in_security supp_dmap).
smt(fdom_map_eq create_handle_inj mem_set get_setE in_correctness in_security supp_dmap).

smt().
smt().
smt().

move => sv.
exfalso => /#.
move => *.
exfalso => /#.
skip; progress.

move => a a'.
if.
done.
sp 2 2.
if.
move => &1 &2.
progress.
smt(syncPoint_same_apiCall).
smt(syncPoint_same_apiCall).
rcondt{1} 5.
move => &m.
auto; progress.
rcondf{2} 4.
move => &m.
auto; progress.
smt(syncPoint_exists_apiCall).
sp 0 3.
match{2}.
move => sv.
exfalso => /#.
exfalso => /#.
move => sv.
rcondt{2} 1.
move => &m.
skip; progress.
smt().
rcondt{2} 3.
move => &m.
auto; progress.
smt(syncPoint_same_apiCall).
rcondt{2} 6.
move => &m.
auto; progress.
rcondt{2} 16.
move => &m.
auto; progress.
sp 0 6.
wp 2 7.

(************************************)
transitivity{1} 
{ (o,tr1) <@ DMapInput.S.map(MPCProtocolLibrary.prot_out (oget Real.senv.[a2]), out_projection); }
(
  (a2{2} = a' /\ ={glob ProgSem, glob Real} /\
   r2{2} = None /\
   a2{1} = a /\
   r1{1} = None /\
   (oget ecall{1} = Call_out a /\
    oget ecall{2} = Call_out a' /\
    (r{2} = None /\
     ecall{2} = syncPoint (allECalls ProgSem.st{2}) /\
     r{1} = None /\
     ecall{1} = syncPoint (allECalls ProgSem.st{1}) /\
     ={ProgSem.st, ProgSem.n} /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        oget Simulator.senv{2}.[v9] =
        take Security.t (oget Real.senv{1}.[v9])) /\
     ProgSem.n{1} = Security.n /\
     ProgSem.st{1}.`StP1 = SPSemantics.st{2}.`sigma /\
     ProgSem.st{1}.`ib = SPSemantics.st{2}.`ib /\
     ProgSem.st{1}.`ob = SPSemantics.st{2}.`ob) /\
    ecall{1} <> None) /\
   ProgSem.st{1}.`ob = None) /\
  (a2{1} \in Real.senv{1})
 ==> ={o,tr1,a2} /\ ={glob ProgSem, glob Real})

(a18{2} = sv /\
  a'1{2} = nshr Security.n (oget Ideal.senv{2}.[a18{2}]) /\
  r15{2} = Some (a'1{2}, Shares a'1{2}) /\
  xxsio1{2} = r15{2} /\
  (xx1{2}, si1{2}) = oget xxsio1{2} /\
  oget cst1{2} = Call_out sv /\
  lst1{2} = SPSemantics.st{2}.`sigma /\
  r6{2} = None /\
  cst1{2} = callSt lst1{2} /\
  (a2{2} = a' /\
   r2{2} = None /\
   a2{1} = a /\
   r1{1} = None /\
   (oget ecall{1} = Call_out a /\
    oget ecall{2} = Call_out a' /\
    (r{2} = None /\
     ecall{2} = syncPoint (allECalls ProgSem.st{2}) /\
     r{1} = None /\
     ecall{1} = syncPoint (allECalls ProgSem.st{1}) /\
     ={ProgSem.st, ProgSem.n} /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        oget Simulator.senv{2}.[v9] =
        take Security.t (oget Real.senv{1}.[v9])) /\
     ProgSem.n{1} = Security.n /\
     ProgSem.st{1}.`StP1 = SPSemantics.st{2}.`sigma /\
     ProgSem.st{1}.`ib = SPSemantics.st{2}.`ib /\
     ProgSem.st{1}.`ob = SPSemantics.st{2}.`ob) /\
    ecall{1} <> None) /\
   ProgSem.st{1}.`ob = None) /\
  (a2{1} \in Real.senv{1})
 ==> 
let tpl = oget (Some (yy{2}, Trace tr0{2})) in
  let tpl0 = oget (Some (o{1}, Trace tr1{1})) in
  let st_L = upd_SigmaAPI Res_out (upd_ob (Some tpl0.`1) ProgSem.st{1}) in
  Some tpl0.`2 = Some tpl.`2 /\
  (st_L = upd_SigmaAPI Res_out (upd_ob (Some tpl.`1) RealSem.st{2}) /\
   ={ProgSem.n}) /\
  (forall (v9 : svar_t), v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
  (forall (v9 : svar_t),
     v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
  (forall (v9 : svar_t),
     v9 \in Real.senv{1} =>
     Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
  (forall (v9 : svar_t),
     v9 \in Real.senv{1} =>
     oget Simulator.senv{2}.[v9] =
     take Security.t (oget Real.senv{1}.[v9])) /\
  ProgSem.n{1} = Security.n /\
  st_L.`StP1 = SPSemantics.st{2}.`sigma /\
  st_L.`ib = SPSemantics.st{2}.`ib /\ st_L.`ob = SPSemantics.st{2}.`ob).

progress.
exists (Ideal.senv{2}) (Real.senv{1}) (Simulator.senv{2}) n (ProgSem.st{2}) (SPSemantics.st{2}) (a2{2}) (syncPoint (allECalls ProgSem.st{2})) None None None. 
smt().
progress.

inline*.
alias{1} 1.
wp. rnd. wp. skip. progress.
cut ->: a2{1} = a2{2}.
smt().
done.
smt().
smt().
smt().
smt().

transitivity{1} 
{ (o,tr1) <@ DMapInput.S.sample(MPCProtocolLibrary.prot_out (oget Real.senv.[a2]), out_projection); }
(
  (a2{2} = a' /\ ={glob ProgSem, glob Real} /\
   r2{2} = None /\
   a2{1} = a /\
   r1{1} = None /\
   (oget ecall{1} = Call_out a /\
    oget ecall{2} = Call_out a' /\
    (r{2} = None /\
     ecall{2} = syncPoint (allECalls ProgSem.st{2}) /\
     r{1} = None /\
     ecall{1} = syncPoint (allECalls ProgSem.st{1}) /\
     ={ProgSem.st, ProgSem.n} /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        oget Simulator.senv{2}.[v9] =
        take Security.t (oget Real.senv{1}.[v9])) /\
     ProgSem.n{1} = Security.n /\
     ProgSem.st{1}.`StP1 = SPSemantics.st{2}.`sigma /\
     ProgSem.st{1}.`ib = SPSemantics.st{2}.`ib /\
     ProgSem.st{1}.`ob = SPSemantics.st{2}.`ob) /\
    ecall{1} <> None) /\
   ProgSem.st{1}.`ob = None) /\
  (a2{1} \in Real.senv{1})
 ==> ={o,tr1,a2} /\ ={glob ProgSem, glob Real})

(a18{2} = sv /\
  a'1{2} = nshr Security.n (oget Ideal.senv{2}.[a18{2}]) /\
  r15{2} = Some (a'1{2}, Shares a'1{2}) /\
  xxsio1{2} = r15{2} /\
  (xx1{2}, si1{2}) = oget xxsio1{2} /\
  oget cst1{2} = Call_out sv /\
  lst1{2} = SPSemantics.st{2}.`sigma /\
  r6{2} = None /\
  cst1{2} = callSt lst1{2} /\
  (a2{2} = a' /\
   r2{2} = None /\
   a2{1} = a /\
   r1{1} = None /\
   (oget ecall{1} = Call_out a /\
    oget ecall{2} = Call_out a' /\
    (r{2} = None /\
     ecall{2} = syncPoint (allECalls ProgSem.st{2}) /\
     r{1} = None /\
     ecall{1} = syncPoint (allECalls ProgSem.st{1}) /\
     ={ProgSem.st, ProgSem.n} /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        oget Simulator.senv{2}.[v9] =
        take Security.t (oget Real.senv{1}.[v9])) /\
     ProgSem.n{1} = Security.n /\
     ProgSem.st{1}.`StP1 = SPSemantics.st{2}.`sigma /\
     ProgSem.st{1}.`ib = SPSemantics.st{2}.`ib /\
     ProgSem.st{1}.`ob = SPSemantics.st{2}.`ob) /\
    ecall{1} <> None) /\
   ProgSem.st{1}.`ob = None) /\
  (a2{1} \in Real.senv{1})
 ==> 
let tpl = oget (Some (yy{2}, Trace tr0{2})) in
  let tpl0 = oget (Some (o{1}, Trace tr1{1})) in
  let st_L = upd_SigmaAPI Res_out (upd_ob (Some tpl0.`1) ProgSem.st{1}) in
  Some tpl0.`2 = Some tpl.`2 /\
  (st_L = upd_SigmaAPI Res_out (upd_ob (Some tpl.`1) RealSem.st{2}) /\
   ={ProgSem.n}) /\
  (forall (v9 : svar_t), v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
  (forall (v9 : svar_t),
     v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
  (forall (v9 : svar_t),
     v9 \in Real.senv{1} =>
     Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
  (forall (v9 : svar_t),
     v9 \in Real.senv{1} =>
     oget Simulator.senv{2}.[v9] =
     take Security.t (oget Real.senv{1}.[v9])) /\
  ProgSem.n{1} = Security.n /\
  st_L.`StP1 = SPSemantics.st{2}.`sigma /\
  st_L.`ib = SPSemantics.st{2}.`ib /\ st_L.`ob = SPSemantics.st{2}.`ob).

move => *.
exists (Ideal.senv{2}) (Real.senv{1}) (Simulator.senv{2}) n (ProgSem.st{2}) (SPSemantics.st{2}) (a2{2}) (syncPoint (allECalls ProgSem.st{2})) None None None. 
smt().
progress.

symmetry.
call (DMapInput.sample).
skip; progress.
smt().
smt().
(************************************)

inline*.
wp.
rnd (fun ot => snd ot) (fun t => (nshr n (oget Ideal.senv{2}.[a18{2}]),t)).
wp; skip; progress.

move : H12.
cut ->: a2{1} = a2{2}.
smt().
cut ->: a18{2} = a2{2}.
smt().
rewrite /shares.
simplify.
rewrite !H5.
smt(). 
rewrite !H4.
smt().
rewrite !oget_some.
smt(out_correctness out_projection_correctness out_projection_supp out_projection_exists out_security out_security_mu1 out_projection_sim_support out_sim_projection_support syncPoint_same_apiCall).
smt(out_correctness out_projection_correctness out_projection_supp out_projection_exists out_security out_security_mu1 out_projection_sim_support out_sim_projection_support syncPoint_same_apiCall).
smt(out_correctness out_projection_correctness out_projection_supp out_projection_exists out_security out_security_mu1 out_projection_sim_support out_sim_projection_support syncPoint_same_apiCall).
smt().
smt().
smt().
smt().
smt().

move => sop pargs sargs.
exfalso => /#.

sp 1 1.
if.
done.
exfalso => /#.
by skip.
by skip.

move => o pp ss o' pp' ss'.
sp 4 4.
if.
progress.
smt().
smt().
smt().
smt().
rcondt{1} 9.
move => &m.
auto; progress.
rcondf{2} 4.
move => &m.
auto; progress.
smt().
sp 0 3.
match{2}.
move => sv.
exfalso => /#.
exfalso => /#.
move => sv.
exfalso => /#.
move => o'' pp'' ss''.
rcondt{2} 5.
move => &m.
auto; progress.
smt().
smt().
rcondt{2} 12.
move => &m.
auto; progress.
rcondt{2} 23.
move => &m.
auto; progress.
sp.
seq 1 1 : (#pre /\ h0{1} \in create_handle (fdom Real.senv{1}) /\ h8{2} \in  create_handle (fdom Ideal.senv{2}) /\ h0{1} = h8{2}).
rnd{1}. rnd{2}.
skip; progress.
apply create_handle_ll.
apply create_handle_ll.
smt(fdom_map_eq create_handle_inj).
sp 1 2.
wp 2 11.

(************************************************)
transitivity{1}
{ (y,tr2) <@ DMapInput.S.map(MPCProtocolLibrary.prot_sop sop pargs (map (fun s => oget Real.senv.[s]) sargs), sop_projection); }

(
  a3{1} = h0{1} /\ ={a3,glob ProgSem, glob Real} /\
  (
   hdls0{1} = fdom Real.senv{1} /\
   (sop{1} = o /\ pargs{1} = pp /\ sargs{1} = ss /\
    sop{2} = sop{1} /\
    pargs{2} = pargs{1} /\
    sargs{2} = sargs{1} /\
    r2{1} = None /\
    oget ecall{1} = Call_sop o pp ss /\
    oget ecall{2} = Call_sop o' pp' ss' /\
    (r{2} = None /\
     ecall{2} = syncPoint (allECalls ProgSem.st{2}) /\
     r{1} = None /\
     ecall{1} = syncPoint (allECalls ProgSem.st{1}) /\
     ={ProgSem.st, ProgSem.n} /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        oget Simulator.senv{2}.[v9] =
        take Security.t (oget Real.senv{1}.[v9])) /\
     ProgSem.n{1} = Security.n /\
     ProgSem.st{1}.`StP1 = SPSemantics.st{2}.`sigma /\
     ProgSem.st{1}.`ib = SPSemantics.st{2}.`ib /\
     ProgSem.st{1}.`ob = SPSemantics.st{2}.`ob) /\
    ecall{1} <> None) /\
   forall (x1 : svar_t), (x1 \in sargs{1}) /\ (x1 \in Real.senv{1})) /\
  (h0{1} \in create_handle (fdom Real.senv{1}))
==> 
={y,tr2,a3,glob ProgSem, glob Real})

(a23{2} = h8{2} /\
  (y3{2}, l3{2}) =
  (sop_spec sop3{2} pargs3{2}
     (map (fun (a24 : svar_t) => oget Ideal.senv{2}.[a24]) sargs3{2}))%MPCProtocolLibrary /\
  a3{1} = h0{1} /\
  (sop3{2} = o'' /\
   pargs3{2} = pp'' /\
   sargs3{2} = ss'' /\
   r19{2} = None /\
   hdls8{2} = fdom Ideal.senv{2} /\
   hdls0{1} = fdom Real.senv{1} /\
   oget cst2{2} = Call_sop o'' pp'' ss'' /\
   lst2{2} = SPSemantics.st{2}.`sigma /\
   r7{2} = None /\
   cst2{2} = callSt lst2{2} /\
   (sop{2} = o' /\
    pargs{2} = pp' /\
    sargs{2} = ss' /\
    r3{2} = None /\
    sop{1} = o /\
    pargs{1} = pp /\
    sargs{1} = ss /\
    r2{1} = None /\
    oget ecall{1} = Call_sop o pp ss /\
    oget ecall{2} = Call_sop o' pp' ss' /\
    (r{2} = None /\
     ecall{2} = syncPoint (allECalls ProgSem.st{2}) /\
     r{1} = None /\
     ecall{1} = syncPoint (allECalls ProgSem.st{1}) /\
     ={ProgSem.st, ProgSem.n} /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        oget Simulator.senv{2}.[v9] =
        take Security.t (oget Real.senv{1}.[v9])) /\
     ProgSem.n{1} = Security.n /\
     ProgSem.st{1}.`StP1 = SPSemantics.st{2}.`sigma /\
     ProgSem.st{1}.`ib = SPSemantics.st{2}.`ib /\
     ProgSem.st{1}.`ob = SPSemantics.st{2}.`ob) /\
    ecall{1} <> None) /\
   forall (x1 : svar_t), (x1 \in sargs{1}) /\ (x1 \in Real.senv{1})) /\
  (h0{1} \in create_handle (fdom Real.senv{1})) /\
  (h8{2} \in create_handle (fdom Ideal.senv{2})) /\ h0{1} = h8{2}
 ==> 
let senv_R = Simulator.senv{2}.[a3{2} <- y{2}] in
  let tpl = oget (Some (a3{2}, Trace tr1{2})) in
  let senv_L = Real.senv{1}.[a3{1} <- y{1}] in
  let tpl0 = oget (Some (a3{1}, Trace tr2{1})) in
  let st_L = upd_SigmaAPI (Res_sop tpl0.`1) ProgSem.st{1} in
  Some tpl0.`2 = Some tpl.`2 /\
  (st_L = upd_SigmaAPI (Res_sop tpl.`1) RealSem.st{2} /\ ={ProgSem.n}) /\
  (forall (v9 : svar_t), v9 \in senv_L <=> v9 \in Ideal.senv{2}) /\
  (forall (v9 : svar_t), v9 \in senv_L <=> v9 \in senv_R) /\
  (forall (v9 : svar_t),
     v9 \in senv_L =>
     Ideal.senv{2}.[v9] = Some (unshr (oget senv_L.[v9]))) /\
  (forall (v9 : svar_t),
     v9 \in senv_L => oget senv_R.[v9] = take Security.t (oget senv_L.[v9])) /\
  ProgSem.n{1} = Security.n /\
  st_L.`StP1 = SPSemantics.st{2}.`sigma /\
  st_L.`ib = SPSemantics.st{2}.`ib /\ st_L.`ob = SPSemantics.st{2}.`ob).

move => *.
exists (Ideal.senv{2}) (Real.senv{1}) (Simulator.senv{2}) n (ProgSem.st{1}) (SPSemantics.st{2}) (a3{1}) (syncPoint (allECalls ProgSem.st{1})) (h0{1}) (fdom Real.senv{1}) (pargs{1}) None None (sargs{1}) (sop{1}).
smt(). 
done.

inline*.
alias{1} 1.
wp. rnd. wp. skip. progress.
smt().
smt().

transitivity{1}
{ (y,tr2) <@ DMapInput.S.sample(MPCProtocolLibrary.prot_sop sop pargs (map (fun s => oget Real.senv.[s]) sargs), sop_projection); }

(
  a3{1} = h0{1} /\ ={a3,glob ProgSem, glob Real} /\
  (
   hdls0{1} = fdom Real.senv{1} /\
   (sop{1} = o /\ pargs{1} = pp /\ sargs{1} = ss /\
    sop{2} = sop{1} /\
    pargs{2} = pargs{1} /\
    sargs{2} = sargs{1} /\
    r2{1} = None /\
    oget ecall{1} = Call_sop o pp ss /\
    oget ecall{2} = Call_sop o' pp' ss' /\
    (r{2} = None /\
     ecall{2} = syncPoint (allECalls ProgSem.st{2}) /\
     r{1} = None /\
     ecall{1} = syncPoint (allECalls ProgSem.st{1}) /\
     ={ProgSem.st, ProgSem.n} /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        oget Simulator.senv{2}.[v9] =
        take Security.t (oget Real.senv{1}.[v9])) /\
     ProgSem.n{1} = Security.n /\
     ProgSem.st{1}.`StP1 = SPSemantics.st{2}.`sigma /\
     ProgSem.st{1}.`ib = SPSemantics.st{2}.`ib /\
     ProgSem.st{1}.`ob = SPSemantics.st{2}.`ob) /\
    ecall{1} <> None) /\
   forall (x1 : svar_t), (x1 \in sargs{1}) /\ (x1 \in Real.senv{1})) /\
  (h0{1} \in create_handle (fdom Real.senv{1}))
==> 
={y,tr2,a3,glob ProgSem, glob Real})

(a23{2} = h8{2} /\
  (y3{2}, l3{2}) =
  (sop_spec sop3{2} pargs3{2}
     (map (fun (a24 : svar_t) => oget Ideal.senv{2}.[a24]) sargs3{2}))%MPCProtocolLibrary /\
  a3{1} = h0{1} /\
  (sop3{2} = o'' /\
   pargs3{2} = pp'' /\
   sargs3{2} = ss'' /\
   r19{2} = None /\
   hdls8{2} = fdom Ideal.senv{2} /\
   hdls0{1} = fdom Real.senv{1} /\
   oget cst2{2} = Call_sop o'' pp'' ss'' /\
   lst2{2} = SPSemantics.st{2}.`sigma /\
   r7{2} = None /\
   cst2{2} = callSt lst2{2} /\
   (sop{2} = o' /\
    pargs{2} = pp' /\
    sargs{2} = ss' /\
    r3{2} = None /\
    sop{1} = o /\
    pargs{1} = pp /\
    sargs{1} = ss /\
    r2{1} = None /\
    oget ecall{1} = Call_sop o pp ss /\
    oget ecall{2} = Call_sop o' pp' ss' /\
    (r{2} = None /\
     ecall{2} = syncPoint (allECalls ProgSem.st{2}) /\
     r{1} = None /\
     ecall{1} = syncPoint (allECalls ProgSem.st{1}) /\
     ={ProgSem.st, ProgSem.n} /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Ideal.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} <=> v9 \in Simulator.senv{2}) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        Ideal.senv{2}.[v9] = Some (unshr (oget Real.senv{1}.[v9]))) /\
     (forall (v9 : svar_t),
        v9 \in Real.senv{1} =>
        oget Simulator.senv{2}.[v9] =
        take Security.t (oget Real.senv{1}.[v9])) /\
     ProgSem.n{1} = Security.n /\
     ProgSem.st{1}.`StP1 = SPSemantics.st{2}.`sigma /\
     ProgSem.st{1}.`ib = SPSemantics.st{2}.`ib /\
     ProgSem.st{1}.`ob = SPSemantics.st{2}.`ob) /\
    ecall{1} <> None) /\
   forall (x1 : svar_t), (x1 \in sargs{1}) /\ (x1 \in Real.senv{1})) /\
  (h0{1} \in create_handle (fdom Real.senv{1})) /\
  (h8{2} \in create_handle (fdom Ideal.senv{2})) /\ h0{1} = h8{2}
 ==> 
let senv_R = Simulator.senv{2}.[a3{2} <- y{2}] in
  let tpl = oget (Some (a3{2}, Trace tr1{2})) in
  let senv_L = Real.senv{1}.[a3{1} <- y{1}] in
  let tpl0 = oget (Some (a3{1}, Trace tr2{1})) in
  let st_L = upd_SigmaAPI (Res_sop tpl0.`1) ProgSem.st{1} in
  Some tpl0.`2 = Some tpl.`2 /\
  (st_L = upd_SigmaAPI (Res_sop tpl.`1) RealSem.st{2} /\ ={ProgSem.n}) /\
  (forall (v9 : svar_t), v9 \in senv_L <=> v9 \in Ideal.senv{2}) /\
  (forall (v9 : svar_t), v9 \in senv_L <=> v9 \in senv_R) /\
  (forall (v9 : svar_t),
     v9 \in senv_L =>
     Ideal.senv{2}.[v9] = Some (unshr (oget senv_L.[v9]))) /\
  (forall (v9 : svar_t),
     v9 \in senv_L => oget senv_R.[v9] = take Security.t (oget senv_L.[v9])) /\
  ProgSem.n{1} = Security.n /\
  st_L.`StP1 = SPSemantics.st{2}.`sigma /\
  st_L.`ib = SPSemantics.st{2}.`ib /\ st_L.`ob = SPSemantics.st{2}.`ob).

move => *.
exists (Ideal.senv{2}) (Real.senv{1}) (Simulator.senv{2}) n (ProgSem.st{1}) (SPSemantics.st{2}) (a3{1}) (syncPoint (allECalls ProgSem.st{1})) (h0{1}) (fdom Real.senv{1}) (pargs{1}) None None (sargs{1}) (sop{1}).
smt(). 
done.

symmetry.
call (DMapInput.sample).
by skip.
(************************************************)

inline*.
wp.
rnd{1}. rnd{2}. (*ugly as fuck*)
wp.
rnd{2}.
wp; skip; progress.
apply create_handle_ll.
apply sim_sop_ll.
rewrite dmap_ll.
apply prot_sop_ll.

move : H19.
rewrite supp_dmap.
progress.
move : (sop_security sop{1} pargs{1} (map (fun (a : svar_t) => oget Real.senv{1}.[a]) sargs{1}) a24.`1 a24.`2 ytr1.`1 ytr1.`2).
cut ->: (a24.`1, a24.`2) \in MPCProtocolLibrary.prot_sop sop{1} pargs{1} (map (fun (a : svar_t) => oget Real.senv{1}.[a]) sargs{1}). smt().
simplify.
rewrite -map_comp /(\o) /=.
cut ->: (fun (x : svar_t) =>
          take SecretSharingScheme.t (oget Real.senv{1}.[x])) = 
        (fun (x : svar_t) => oget Simulator.senv{2}.[x]).
rewrite fun_ext /(==).
move => x.
case (x \in  sargs{1}) => ?.
smt().
smt().
rewrite -map_comp /(\o) /=.
cut ->: (fun (x : svar_t) => unshr (oget Real.senv{1}.[x])) = 
        (fun (a : svar_t) => oget Ideal.senv{2}.[a]).
rewrite fun_ext /(==).
move => x.
case (x \in  sargs{1}) => ?.
have ?: (x \in Real.senv{1}).
smt().
smt().
smt().
cut ->: (MPCProtocolLibrary.sop_spec sop{1} pargs{1}
        (map (fun (a : svar_t) => oget Ideal.senv{2}.[a]) sargs{1})).`2 = l3{2}.
move : H.
cut ->: sop{1} = sop3{2}.
smt(syncPoint_same_apiCall).
cut ->: pargs{1} = pargs3{2}.
smt(syncPoint_same_apiCall).
cut ->: sargs{1} = sargs3{2}.
smt(syncPoint_same_apiCall).
smt().
cut ->: (ytr1.`1, ytr1.`2) \in MPCProtocolLibrary.sim_sop sop{1} pargs{1} (map (fun (x : svar_t) => oget Simulator.senv{2}.[x]) sargs{1}) l3{2}.
smt().
simplify.
rewrite /sop_projection.
move : H19.
elim a24 => yy tr.
simplify.
smt().

smt(fdom_map_eq create_handle_inj).
smt(fdom_map_eq create_handle_inj mem_set).
smt(fdom_map_eq create_handle_inj mem_set).
smt(fdom_map_eq create_handle_inj mem_set).
smt(fdom_map_eq create_handle_inj mem_set).

rewrite mem_set in H20.
move : H19.
rewrite supp_dmap.
progress.
move : H19.
elim a24 => yy tr.
simplify.
progress.
cut ->: y3{2} = (MPCProtocolLibrary.sop_spec sop3{2} pargs3{2}
       (map (fun (a24 : svar_t) => oget Ideal.senv{2}.[a24]) sargs3{2})).`1.
smt().
cut ->: sop3{2} = sop{1}.
smt(syncPoint_same_apiCall).
cut ->: pargs3{2} = pargs{1}.
smt(syncPoint_same_apiCall).
cut ->: sargs3{2} = sargs{1}.
smt(syncPoint_same_apiCall).
move : (sop_correctness sop{1} pargs{1} (map (fun (s : svar_t) => oget Real.senv{1}.[s]) sargs{1}) yy tr).
rewrite H19 /=.
rewrite -map_comp /(\o) /=.
cut ->: (fun (x : svar_t) => unshr (oget Real.senv{1}.[x])) = 
        (fun (a : svar_t) => oget Ideal.senv{2}.[a]).
rewrite fun_ext /(==).
move => x.
case (x \in  sargs{1}) => ?.
have ?: (x \in Real.senv{1}).
smt().
smt().
smt().
simplify => *.
rewrite -H21.
rewrite /sop_projection.
simplify.
smt(get_setE).

rewrite mem_set in H20.
move : H19.
rewrite supp_dmap.
progress.
move : H19.
elim a24 => yy tr.
simplify.
progress.
cut ->: h00 = h8{2}.
smt(fdom_map_eq create_handle_inj).
rewrite !get_setE.
case (v9 = h8{2}) => ?.
rewrite !oget_some.
rewrite /sop_projection.
simplify.
move : (sop_security sop{1} pargs{1} (map (fun (s : svar_t) => oget Real.senv{1}.[s]) sargs{1}) yy tr ytr1.`1 ytr1.`2).
rewrite H19 /=.
rewrite -map_comp /(\o) /=.
cut ->: (fun (x : svar_t) =>
          take SecretSharingScheme.t (oget Real.senv{1}.[x])) = 
        (fun (x : svar_t) => oget Simulator.senv{2}.[x]).
rewrite fun_ext /(==).
move => x.
case (x \in  sargs{1}) => ?.
smt().
smt().
rewrite -map_comp /(\o) /=.
cut ->: (fun (x : svar_t) => unshr (oget Real.senv{1}.[x])) = 
        (fun (a : svar_t) => oget Ideal.senv{2}.[a]).
rewrite fun_ext /(==).
move => x.
case (x \in  sargs{1}) => ?.
have ?: (x \in Real.senv{1}).
smt().
smt().
smt().
cut ->: (MPCProtocolLibrary.sop_spec sop{1} pargs{1}
        (map (fun (a : svar_t) => oget Ideal.senv{2}.[a]) sargs{1})).`2 = l3{2}.
move : H.
cut ->: sop{1} = sop3{2}.
smt(syncPoint_same_apiCall).
cut ->: pargs{1} = pargs3{2}.
smt(syncPoint_same_apiCall).
cut ->: sargs{1} = sargs3{2}.
smt(syncPoint_same_apiCall).
smt().
cut ->: (ytr1.`1, ytr1.`2) \in MPCProtocolLibrary.sim_sop sop{1} pargs{1} (map (fun (x : svar_t) => oget Simulator.senv{2}.[x]) sargs{1}) l3{2}.
smt().
simplify.
smt().
smt().

smt().
smt().
smt().
smt().

sp 1 1.
if.
done.
exfalso => /#.
by skip.

by skip.

skip; progress.
smt(mem_empty).
smt(mem_empty).
smt(mem_empty).
smt(mem_empty).
qed.

end section Security.

end Security.
