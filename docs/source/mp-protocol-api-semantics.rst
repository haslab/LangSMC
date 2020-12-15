Multi-party protocol API semantics
===================================================================================

In line of what was done for the single-party semantics, we also refine the multi-party
API semantics to support the interaction with a concrete API that relies on a collection of MPC protocols.

A natural restriction regarding the three party-specific language involved in the multi-party semantics is that
the languages should share the same public and secret types, the same input and output types and the same
secret operators.

An example on how a party-specific language is loaded for one party is displayed bellow.
The remaining languages are analogous.

::

  clone import Language as L1 with
    type public_t = value_t,
    type secret_t = sharedValue_t,
    type sop_t = sop_t,
    type inputs_t = sharedValue_t,
    type outputs_t = sharedValue_t.

Armed with the three languages involved in the collaborative program evaluation, we can realize the multi-party
API semantics with the three languages and with the protocol API data.

::

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
    op API.apiRes = apiRes.

With the purpose of checking check if all local party configurations are waiting to perform the same API call, we
introduce the notion of synchronisation points. Informally, reaching a synchronisation point (all parties are waiting
to perform an API operation) the semantics will check if the all parties filled their call data with the same operation.

::

  op syncPoint (api_calls : apiCall_data option * apiCall_data option * apiCall_data option): apiCall_data option =
    let (api_call1, api_call2, api_call3) = api_calls in
    if (api_call1 = api_call2 /\ api_call2 = api_call3) then api_call1 else None.

Finally, we can write a concrete multi-party semantics module that evaluates a program by resorting on the protocol API to perform secure operations over confidential
data, similarly to what we did for the single-party scenario. In a nutshel, the multi-party semantics module will invoke the local semantics of each party when a local
step is requested (providing that the party is not halted at some API call). For synchronised evaluation steps, the semantics first checks if all parties are at the same
synchronisation point and, if this is the case, invokes the API accordingly.

::

  module ProgSem (API: API_t) : Semantics = {

    var n: int
    var st: GlobalSt

    proc init(Prog1: L1.L, Prog2: L2.L, Prog3: L3.L): unit = {
      API.init();
      n <- API.nparties();
      st <- init_GlobalSt Prog1 Prog2 Prog3;
    }

    proc stepP(id: partyId_t): bool = {
      ...
      lst1 <- StP1 st;
      lst2 <- StP2 st;
      lst3 <- StP3 st;

      match (id) with
      | P1 => { if (SemP1.callSt lst1 = None) {
                       newst1 <- SemP1.stepL (SemP1.progSt lst1) (SemP1.envSt lst1) (SemP1.resSt lst1);
                       if (newst1 <> None) { r <- true; st <- upd_Sigma1 (oget newst1) st; } } }
      | P2 => ...
      | P3 => ...
      end;

      return r;
    }

    proc stepS(): sideInfo_t option = {
      ...
      var ecall <- syncPoint (allECalls st);
      if (ecall <> None) { 
        match (oget ecall) with
        | Call_declass a => { vto <@ API.declass(a);
                              if (vto <> None) {
                                (v, tr) <- oget vto;
                                r <- Some tr;
                                (* updates API result *)
                                st <- upd_SigmaAPI (Some v) st; } }
        | Call_in a => ...
        | Call_out a => ...
        | Call_sop o a pargs sargs => ...
        end;
      }
      return r;
    }
    proc setInput(x: inputs_t): bool = {
      var r <- false;
      if (ib st = None) {  r <- true; st <- upd_ib (Some x) st; }
      return r;
    }
    proc getOutput(): outputs_t option = {
      ...
      r <- ob st;
      if (r <> None) { st <- upd_ob None st; }
      return r;
    }
  }.
