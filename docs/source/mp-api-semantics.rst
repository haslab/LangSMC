Multi-party API semantics
======================================================================

Similarly to the single-party semantics, we define a particular multi-party semantics that works for languages
where the computation of secret operations is carried out
by an external API, whilst public operations remain in the
domain of the language itself. This semantics is essentially a realisation of the multiparty
semantics, that extends it with new datatypes and operations to interpolate 
between the evaluation of the program and the API calls that are requested.

At a high level, the multi-party API semantics is compose by three copies of the 
single-party API semantics (one for each computing party). Each party will have its own API interaction buffers, which is
written every time local computation reaches a secret operation. When
all parties fill their buffers, the API can proceed with the secret operation
computation, writing the individual outputs in the respective party
buffer. Observe that, in order for such interpolation to be realisable,
every local semantics must be given access to the same API module and their
local API interaction buffers must be of the same type.

An example on how a single-party API semantics is loaded for one party is displayed bellow.
The remaining semantics are analogous.

::

  (** Language L1 *)
  clone import Language as L1.
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

Semantics configuration comprises the local configuration of each party
semantics, together with an input and output buffers, that override the
respective input and output buffers of local semantics, as detailed by the ``GlobalSt`` type. An update to a
configuration can be derived from either local party execution - ``updSigma1``, ``updSigma2`` and ``updSigma3`` for
updating information with respect to party 1, 2 and 3, respectively - , synchronised
computation - ``upd_SigmaAPI`` -, or input and output commands - ``upd_ib`` and ``upd_ob``.

::

  type GlobalSt = { StP1 : SemP1.StateL
                    ; StP2 : SemP2.StateL
                    ; StP3 : SemP3.StateL
                    ; ib : inputs_t option
                    ; ob : outputs_t option }.

  (** Updates a local state after a [stepP] *)
  op upd_Sigma1 (newst1 : (L1.L, SemP1.EnvL) ECall) (st: GlobalSt): GlobalSt =
    {| st with StP1 = SemP1.st_from_step newst1 | }.
  op upd_Sigma2 (newst2 : (L2.L, SemP2.EnvL) ECall) (st: GlobalSt): GlobalSt =
    {| st with StP2 = SemP2.st_from_step newst2 | }.
  op upd_Sigma3 (newst3 : (L3.L, SemP3.EnvL) ECall) (st: GlobalSt): GlobalSt =
    {| st with StP3 = SemP3.st_from_step newst3 | }.    

  (** Updates all local states after a [stepS] *)
  op upd_SigmaAPI (r: apiRes_data option) (st: GlobalSt): GlobalSt =
    {| st with StP1 = SemP1.updRes r st.`StP1 ; StP2 = SemP2.updRes r st.`StP2 ; StP3 = SemP3.updRes r st.`StP3 | }.

  (** Updates the input buffer *)
  op upd_ib (newib: inputs_t option) (st: GlobalSt): GlobalSt =
    {| st with ib = newib | }.

  (** Updates the output buffer *)
  op upd_ob (newob: outputs_t option) (st: GlobalSt): GlobalSt =
    {| st with ob = newob | }.

Finally, we provide methods to initialise the global evaluation state by invoking each party
local semantic initialisation method and also an operator to collect the current API call state of each
party.

::

  (** Initialises all local party states *)
  op init_GlobalSt (Prog1: L1.L) (Prog2: L2.L) (Prog3: L3.L) : GlobalSt =
    {| StP1 = SemP1.initSt (SemP1.initStateL Prog1)
       ; StP2 = SemP2.initSt (SemP2.initStateL Prog2)
       ; StP3 = SemP3.initSt (SemP3.initStateL Prog3)
       ; ib = None
       ; ob = None |}.

  (** Collects all API calls from the local states *)
  op allECalls (st: GlobalSt) : apiCall_data option * apiCall_data option * apiCall_data option =
    (SemP1.callSt st.`StP1, SemP2.callSt st.`StP2, SemP3.callSt st.`StP3).

