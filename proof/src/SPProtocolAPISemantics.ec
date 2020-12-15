require import AllCore List SmtMap.

require import AAPI ALanguage ASPSemantics SPAPISemantics AProtocolLibrary ProtocolAPI.

theory SinglePartyProtocolAPISemantics.

  clone import Language.

  clone import ProtocolLibrary with
    type value_t = public_t,
    type inputs_t = secret_t,
    type outputs_t = secret_t,
    type sop_t = sop_t.

  clone import ProtocolAPI with
    op ProtocolLibrary.n = n,
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
  import API.

  clone import SinglePartyAPISemantics with
    theory Language <- Language,
    type API.public_t = public_t,
    type API.inputs_t = inputs_t,
    type API.outputs_t = outputs_t,
    type API.svar_t = svar_t,
    type API.sop_t = sop_t,
    type API.sideInfo_t = sideInfo_t,
    type API.apiCall_data = apiCall_data,
    type API.apiRes_data = apiRes_data,
    type API.apiCallRes = apiCallRes,
    op API.apiCall = ProtocolAPI.apiCall,
    op API.apiRes = ProtocolAPI.apiRes.
  import API.

  module SPSemantics (API : API_t) = {

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
        if (newst <> None) { st <- upd_sigma (oget newst) st; }
      }
      else {
        match (oget cst) with
        | Call_declass a => { vsio <@ API.declass(a); 
                               if (vsio <> None) {
                                 (v, si) <- oget vsio;
                                 st <- upd_SigmaAPI (Some v) st; 
                                 r <- Some si; } }
        | Call_in a => { if (ib st <> None) {
                         asio <@ API.input(a, oget (ib st)); 
                         if (asio <> None) {
                           si <- oget asio;
                           st <- upd_ib None st;
                           st <- upd_SigmaAPI None st; 
                           r <- Some si; } } }
        | Call_out a => { if (ob st = None) {
                            xxsio <@ API.output(a);
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

end SinglePartyProtocolAPISemantics.
