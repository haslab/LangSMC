(** Multiparty semantics for a language parameterised by an API *)
require import AllCore List SmtMap.

require import AAPI ALanguage AMPSemantics SPAPISemantics.

(**
  We define a particular multiparty semantics that works for languages
  where the computation of secret operations is carried out
  by an external API, whlist public operations remain in the
  domain of the language itself.

  This semantics is essentially a realisation of the multiparty
  semantics, that extends it with new datatypes and operations to interpolate 
  between the evaluation of the program and the API calls that are requested.

  The interaction with the API is done via the [apiCallRes] buffer, with
  each party having their own API interaction buffers. These buffers are
  written everytime local computation reaches a secret operation. When
  all parties fill their buffers, the API can proceed with the secret operation
  computation, writing the individual outputs in the respective party
  buffer. Observe that, in order for such interpolation to be realisable,
  every local semantics must be given access to the same API module and their
  local API interaction buffers must be of the same type.

  Semantics configuration comprises the local configuration of each party
  semantics, together with an input and output buffers, that override the
  respective input and output buffers of local semantics. An update to a
  configuration can be derived from either local party execution, synchronised
  computation, or input and output commands.
*)
theory MultiPartyAPISemantics.

  (** Language L1 *)
  clone import Language as L1.

  (** Language L2 *)
  clone import Language as L2.

  (** Language L3 *)
  clone import Language as L3.

  (** API *)
  clone import API.

  (** Semantics of programs written in L1 *)
  clone import SinglePartyAPISemantics as SemP1 with
    theory Language <- L1,
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

  (** Semantics of programs written in L2 *)
  clone import SinglePartyAPISemantics as SemP2 with
    theory Language <- L2,
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

  (** Semantics of programs written in L3 *)
  clone import SinglePartyAPISemantics as SemP3 with
    theory Language <- L3,
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

  (** Party identifier *)
  type partyId_t.

  (** Global configuration *)
  type GlobalSt = { StP1 : SemP1.StateL
                    ; StP2 : SemP2.StateL
                    ; StP3 : SemP3.StateL
                    ; ib : inputs_t option
                    ; ob : outputs_t option
                  }.

  (** Updates a local state after a [stepP] *)
  op upd_Sigma1 (newst1 : (L1.L, SemP1.EnvL) ECall) (st: GlobalSt): GlobalSt =
    {| st with StP1 = SemP1.st_from_step newst1 |}.
  op upd_Sigma2 (newst2 : (L2.L, SemP2.EnvL) ECall) (st: GlobalSt): GlobalSt =
    {| st with StP2 = SemP2.st_from_step newst2 |}.
  op upd_Sigma3 (newst3 : (L3.L, SemP3.EnvL) ECall) (st: GlobalSt): GlobalSt =
    {| st with StP3 = SemP3.st_from_step newst3 |}.    

  (** Updates all local states after a [stepS] *)
  op upd_SigmaAPI (r: apiRes_data option) (st: GlobalSt): GlobalSt =
    {| st with StP1 = SemP1.updRes r st.`StP1 ; StP2 = SemP2.updRes r st.`StP2 ; StP3 = SemP3.updRes r st.`StP3 |}.

  (** Updates the input buffer *)
  op upd_ib (newib: inputs_t option) (st: GlobalSt): GlobalSt =
    {| st with ib = newib |}.

  (** Updates the output buffer *)
  op upd_ob (newob: outputs_t option) (st: GlobalSt): GlobalSt =
    {| st with ob = newob |}.

  (** Collects all API calls from the local states *)
  op allECalls (st: GlobalSt) : apiCall_data option * apiCall_data option * apiCall_data option =
    (SemP1.callSt st.`StP1, SemP2.callSt st.`StP2, SemP3.callSt st.`StP3).

  (** Initialises all local party states *)
  op init_GlobalSt (Prog1: L1.L) (Prog2: L2.L) (Prog3: L3.L) : GlobalSt =
    {| StP1 = SemP1.initSt (SemP1.initStateL Prog1)
       ; StP2 = SemP2.initSt (SemP2.initStateL Prog2)
       ; StP3 = SemP3.initSt (SemP3.initStateL Prog3)
       ; ib = None
       ; ob = None
    |}.
  
  (** Semantics realisation *)
  clone import MultiPartySemantics with
    theory L1 <- L1,
    theory L2 <- L2,
    theory L3 <- L3,
    type sideInfo_t = sideInfo_t,
    type partyId_t = partyId_t.
 
end MultiPartyAPISemantics.
