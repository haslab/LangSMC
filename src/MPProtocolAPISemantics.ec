require import AllCore List SmtMap.

require import AAPI ALanguage AMPSemantics MPAPISemantics AProtocolLibrary ProtocolAPI.
require import MPCProtocolLibrary ASecretSharingScheme.
require import Utils.

import SS.
import MPCLib.
import MPCAPI.

theory MultiPartyProtocolAPISemantics.

  (*type partyId_t = partyId_t.

  clone import SecretSharingScheme with
    type partyId_t = partyId_t,
    op n = 3,
    op t = 1.

  clone import MPCProtocolLibrary with
    type SecretSharingScheme.partyId_t = partyId_t,
    op SecretSharingScheme.n = 3,
    op SecretSharingScheme.t = 1,
    type SecretSharingScheme.value_t = value_t,
    type SecretSharingScheme.share_t = share_t,
    op SecretSharingScheme.nshr = nshr,
    op SecretSharingScheme.unshr = unshr.*)

  (** Language L1 *)
  clone import Language as L1 with
    type public_t = value_t,
    type secret_t = sharedValue_t,
    type sop_t = sop_t,
    type inputs_t = sharedValue_t,
    type outputs_t = sharedValue_t.

  (** Language L2 *)
  clone import Language as L2 with
    type public_t = value_t,
    type secret_t = sharedValue_t,
    type sop_t = sop_t,
    type inputs_t = sharedValue_t,
    type outputs_t = sharedValue_t.

  (** Language L3 *)
  clone import Language as L3 with
    type public_t = value_t,
    type secret_t = sharedValue_t,
    type sop_t = sop_t,
    type inputs_t = sharedValue_t,
    type outputs_t = sharedValue_t.

(*  clone import ProtocolLibrary with
    op n = 3,
    type partyId_t = partyId_t,
    type value_t = public_t,
    type inputs_t = secret_t,
    type outputs_t = secret_t,
    type sop_t = sop_t.*)

  (*clone import ProtocolAPI with
    op ProtocolLibrary.n = MPCProtocolLibrary.n,
    type ProtocolLibrary.partyId_t = partyId_t,
    type ProtocolLibrary.value_t = value_t,
    type ProtocolLibrary.inputs_t = inputs_t,
    type ProtocolLibrary.outputs_t = outputs_t,
    type ProtocolLibrary.msg_data = msg_data,
    type ProtocolLibrary.leakage_t = leakage_t,
    type ProtocolLibrary.sideInfo_t = sideInfo_t,
    type ProtocolLibrary.sop_t = sop_t,
    op ProtocolLibrary.sop_spec = sop_spec,
    op ProtocolLibrary.prot_declass = prot_declass,
    op ProtocolLibrary.prot_in = prot_in,
    op ProtocolLibrary.prot_out = prot_out,
    op ProtocolLibrary.prot_sop = prot_sop,
    op ProtocolLibrary.sim_declass = sim_declass,
    op ProtocolLibrary.sim_in = sim_in,
    op ProtocolLibrary.sim_out = sim_out,
    op ProtocolLibrary.sim_sop = sim_sop.
  import API.*)

  clone import MultiPartyAPISemantics with
    theory L1 <- L1,
    theory L2 <- L2,
    theory L3 <- L3,
    type partyId_t = partyId_t,
    type API.public_t = public_t,
    type API.inputs_t = inputs_t,
    type API.outputs_t = outputs_t,
    type API.svar_t = svar_t,
    type API.sop_t = sop_t,
    type API.sideInfo_t = sideInfo_t,
    type API.apiCall_data = apiCall_data,
    type API.apiRes_data = apiRes_data,
    type API.apiCallRes = apiCallRes,
    op API.apiCall = apiCall,
    op API.apiRes = apiRes,
    op SemP1.updRes (x: apiRes_data option) (st: ('a,'b) APIst) = (omap ApiRes x, st.`2),
    op SemP1.st_from_step (x: ('a,'b) ECall) = (omap ApiCall x.`1, (x.`2.`1, x.`2.`2)),
    op SemP2.updRes (x: apiRes_data option) (st: ('a,'b) APIst) = (omap ApiRes x, st.`2),
    op SemP2.st_from_step (x: ('a,'b) ECall) = (omap ApiCall x.`1, (x.`2.`1, x.`2.`2)),
    op SemP3.updRes (x: apiRes_data option) (st: ('a,'b) APIst) = (omap ApiRes x, st.`2),
    op SemP3.st_from_step (x: ('a,'b) ECall) = (omap ApiCall x.`1, (x.`2.`1, x.`2.`2)).
  import API.
  import MultiPartySemantics.

  (** Synchronisation points *)
  (** 
    Synchronisation points are used to check if all local
    party configurations are waiting to perform the same API
    call
  *)
  op syncPoint (api_calls : apiCall_data option * apiCall_data option * apiCall_data option): apiCall_data option =
    let (api_call1, api_call2, api_call3) = api_calls in
    if (api_call1 = api_call2 /\ api_call2 = api_call3) then api_call1 else None.

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
    proc stepS(): sideInfo_t option = {
      var x, v, tr;
      var vto, ato, xto;
      var r <- None;
      var ecall <- syncPoint (allECalls st);
      if (ecall <> None) { (* call to the API *)
        match (oget ecall) with
        | Call_declass a => { vto <@ API.declass(a);
                              if (vto <> None) {
                                (v, tr) <- oget vto;
                                r <- Some tr;
                                (* updates API result *)
                                st <- upd_SigmaAPI (Some v) st;
                              }
                            }
        | Call_in a => { if (ib st <> None) {
                           ato <@ API.input(a, oget (ib st));
                           if (ato <> None) {
                             tr <- oget ato;
                             r <- Some tr;
                             st <- upd_ib None st; (* clears buffer *)
                             st <- upd_SigmaAPI None st; (* resets call *)
                           }
                         }
                       }
        | Call_out a => { if (ob st = None) {
                            xto <@ API.output(a);
                            if (xto <> None) {
                              (x, tr) <- oget xto;
                              r <- Some tr;
                              st <- upd_ob (Some x) st; (* fills buffer *)
                              st <- upd_SigmaAPI None st; (* resets call *)
                            }
                          }
                        }
        | Call_sop o a pargs sargs => { ato <@ API.sop(o, pargs, sargs, a);
                                      if (ato <> None) {
                                        tr <- oget ato;
                                        r <- Some tr;
                                        st <- upd_SigmaAPI None st; (* resets call *)
                                      }
                                    }
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

end MultiPartyProtocolAPISemantics.
