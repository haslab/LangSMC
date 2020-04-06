(** Single party semantics for a language parameterised by an API *)
require import AllCore List SmtMap.

require import AAPI ALanguage ASPSemantics.

(**
  We define a particular single party semantics that works for languages
  where the computation of secret operations is carried out
  by an external API, whlist public operations remain in the
  domain of the language.

  This semantics extends the single party semantics class with 
  new datatypes and operations to interpolate between the evaluation 
  of the program and the API calls that are requested.

  The interaction with the API is done via the [apiCallRes] buffer. To
  manage API calls, the single party semantics is extended maintain an
  API state [APIst], that keeps track of the [apiCallRes] buffer value.

  Semantics configuration comprises the program environment, the status
  of API calls or responses, and the input and output buffer. Updates to
  a configuration can be derived from the interpretation of a program
  instruction or from an input and output commands.

  Finally, our single party API semantics also discloses an operator 
  [stepL] whose role is to model the small-step execution of the program.
  Every instruction of the program produces a new non-API (public)
  environment and a possible API call. If no API call is generated, then
  the program execution can continue, whereas if some API call is generated
  then the semantics must query the API in order to compute some confidential
  operation. Defining semantics execution based on an operator forces it to
  be deterministic, which, altough is not mandatory, it is essential for the
  security and compilation results we want to demonstrate.
*)
theory SinglePartyAPISemantics.

  (** Language *)
  clone import Language.

  (** API *) 
  clone import API.

  (** Augment language with external-call suspensions *)
  type ('a, 'b) ECall = apiCall_data option * ('a * 'b).

  (** The internal state might hold wither a "call" or "result" *)
  type ('a, 'b) APIst = apiCallRes option * ('a * 'b).

  (** State projections *)
  op callSt ['a,'b] (st: ('a,'b) APIst) : apiCall_data option = obind apiCall st.`1.
  op resSt ['a,'b] (st: ('a,'b) APIst) : apiRes_data option = obind apiRes st.`1.
  op progSt ['a,'b] (st: ('a,'b) APIst): 'a = st.`2.`1.
  op envSt ['a,'b] (st: ('a,'b) APIst): 'b = st.`2.`2.

  (** Updates the result of the API *)
  op updRes (x: apiRes_data option) (st: ('a,'b) APIst) : ('a,'b) APIst.

  (** Resulting state from a step action *)
  op st_from_step (x: ('a,'b) ECall) : ('a,'b) APIst.

  (** Environment *)
  type EnvL.

  (** Evaluation state *)
  type StateL = (L, EnvL) APIst.

  (** Initial evaluation state *)
  op initStateL (P:L): (L*EnvL).

  (**  *)
  op initSt ['l,'e] (st0: 'l*'e): ('l,'e) APIst = (None,st0).

  (** Local semantics *)
  (**
    Local party execution takes the language of the party, the
    current party state and produces a new state with a possible
    API call.
  *)
  op stepL : L -> EnvL -> apiRes_data option -> ((L,EnvL) ECall) option.
  
  (** Semantics configuration *)
  type configuration_t = { sigma : StateL ; ib : inputs_t option ; ob : outputs_t option }.

  (** Initial configuration *)
  op initial_configuration (P : L) = {| sigma = initSt (initStateL P) ; ib = None ; ob = None |}.

  (** Updates a local state after a [stepP] *)
  op upd_sigma (newst : (L, EnvL) ECall) (st: configuration_t): configuration_t =
    {| st with sigma = st_from_step newst |}.

  (** Updates all local states after a [stepS] *)
  op upd_SigmaAPI (r: apiRes_data option) (st: configuration_t): configuration_t =
    {| st with sigma = updRes r (sigma st) |}.

  (** Updates the input buffer *)
  op upd_ib (newib: inputs_t option) (st: configuration_t): configuration_t =
    {| st with ib = newib |}.

  (** Updates the output buffer *)
  op upd_ob (newob: outputs_t option) (st: configuration_t): configuration_t =
    {| st with ob = newob |}.

  (** Semantics realisation *)
  clone import SinglePartySemantics with
    theory Language <- Language,
    type sideInfo_t = sideInfo_t.
 
end SinglePartyAPISemantics.
