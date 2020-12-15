Single-party API semantics
=======================================================================

We define a particular single party semantics that works for languages
where the computation of secret operations is carried out
by an external API, whlist public operations remain in the
domain of the language. This semantics extends the single party semantics class with 
new datatypes and operations to interpolate between the evaluation 
of the program and the API calls that are requested.

The interaction with the API is done via the ``apiCallRes`` buffer and
``apiCall_data`` information, intrinsic values to the API. Consequently,
to manage API calls, the single party semantics is extended to maintain an
API state ``APIst``, that keeps track of the ``apiCallRes`` buffer
value, and an external-call suspension ``ECall``. We also provide
methods to collect values from the API state.

::

  type ('a, 'b) ECall = apiCall_data option * ('a * 'b).
  type ('a, 'b) APIst = apiCallRes option * ('a * 'b).

  (** State projections *)
  op callSt ['a,'b] (st: ('a,'b) APIst) : apiCall_data option = obind apiCall st.`1.
  op resSt ['a,'b] (st: ('a,'b) APIst) : apiRes_data option = obind apiRes st.`1.
  op progSt ['a,'b] (st: ('a,'b) APIst): 'a = st.`2.`1.
  op envSt ['a,'b] (st: ('a,'b) APIst): 'b = st.`2.`2.

  (** Updates the result of the API *)
  op updRes (x: apiRes_data option) (st: ('a,'b) APIst) : ('a,'b) APIst.


Semantics configuration comprises the program environment ``EnvL``,
the ovearll evaluation state ``StateL`` comprising the status
of API calls or responses, and the input and output buffer. Updates to
a configuration can be derived from the interpretation of a program
instruction or from an input and output commands.

::

  type EnvL.
  type StateL = (L, EnvL) APIst.

The single-party API semantics also discloses an operator 
``stepL`` whose role is to model the small-step execution of the program.
Every instruction of the program produces a new non-API (public)
environment and a possible API call. If no API call is generated, then
the program execution can continue, whereas if some API call is generated
then the semantics must query the API in order to compute some confidential
operation. Defining semantics execution based on an operator forces it to
be deterministic, which, altough is not mandatory, it is essential for the
security and compilation results we want to demonstrate. We also
provide an operator to update the API state with the call information
that is given by an execution of a step action. 

::

  op stepL : L -> EnvL -> apiRes_data option -> ((L,EnvL) ECall) option.

  (** Resulting state from a step action *)
  op st_from_step (x: ('a,'b) ECall) : ('a,'b) APIst.

As a mean to encapsulate the execution of multiple steps in the
program evaluation, we augment the semantics with the ``stepPiter``
function, that executes ``k`` steps and returns as output the
resulting  API interaction state.

::

  op stepPiter
    (step: L -> EnvL -> apiRes_data option -> ((L,EnvL) ECall) option)
    (k:int)
    (st:(L,EnvL) APIst)
    : (L,EnvL) APIst option =
    Int.IterOp.iter k
      (fun ost => if ost <> None && callSt (oget ost) = None
                  then let st = oget ost in 
                     let ecall = step (progSt st) (envSt st) (resSt st) in
                     omap st_from_step ecall else None) (Some st).

Finally, we specify a new type ``configuration_t`` that encompasses the necessary
evaluation-aware information, including the
evaluation state, the input buffer and the output buffer. In addition
to the semantics configuration type, we also provide methods to update
it with a new local state, a new API state, a new input buffer and a
new output buffer.
  
::

  type configuration_t = { sigma : StateL ; ib : inputs_t option ; ob : outputs_t option }.

  (** Initial configuration *)
  op initial_configuration (P : L) = { | sigma = initSt (initStateL P) ; ib = None ; ob = None | }.

  (** Updates a local state after a [stepP] *)
  op upd_sigma (newst : (L, EnvL) ECall) (st: configuration_t): configuration_t = {| st with sigma = st_from_step newst | }.

  (** Updates all local states after a [stepS] *)
  op upd_SigmaAPI (r: apiRes_data option) (st: configuration_t): configuration_t = {| st with sigma = updRes r (sigma st) | }.

  (** Updates the input buffer *)
  op upd_ib (newib: inputs_t option) (st: configuration_t): configuration_t = {| st with ib = newib | }.

  (** Updates the output buffer *)
  op upd_ob (newob: outputs_t option) (st: configuration_t): configuration_t = {| st with ob = newob | }.
