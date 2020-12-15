Single-party protocol API semantics
=================================================================================

Before stepping into concrete security and compilation proofs, we perform yet another refinement
to our single-party semantics definition, by instantiating the single-party API semantics with a concrete
API that relies on a collection of MPC protocols. Such refinement is done first by importing a *valid* (i.e., with
the correct type correspondence) protocol library

::

  (** Language *)
  clone import Language.

  (** Protocol library that evaluates language values and secret operators *)
  clone import ProtocolLibrary with
    type value_t = public_t,
    type inputs_t = secret_t,
    type outputs_t = secret_t,
    type sop_t = sop_t.

Next, we can define a concrete protocol API that uses the protocols disclosed by the protocol library

::

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

And, finally, we instantiate the single-party API semantics with the protocol API.

::

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

Interestingly, although we are using underspecified MPC protocols to define the protocol API, we can still provide a concrete
semantics module that evaluates a program by resorting on the protocol API to perform secure operations over confidential
data, as shown bellow. In order to perform local computations over non-secret data, the semantics module uses the ``stepL`` operator
given as part of the single-party API semantics.

::

  module SPSemantics (API : API_t) = {

    var st : configuration_t

    proc init(P : L) : unit = {
      st <- initial_configuration P;
      API.init();
    }
    proc step() : sideInfo_t option = {
      ...
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
        | Call_in a => ...
        | Call_out a => ...
        | Call_sop sop a pargs sargs => ...
        end;
      }
      return r;
    }
    proc setInput(x: inputs_t): bool = {
      var r <- false;
      if (ib st = None) { r <- true; st <- upd_ib (Some x) st; }
      return r;
    }
    proc getOutput(): outputs_t option = {
      var r: outputs_t option;
      r <- ob st;
      if (r <> None) { st <- upd_ob None st; }
      return r;
    }
  }.
