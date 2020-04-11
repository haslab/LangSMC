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

(* multiple steps... *)
op stepPiter
  (step: L -> EnvL -> apiRes_data option -> ((L,EnvL) ECall) option)
  (k:int)
  (st:(L,EnvL) APIst)
  : (L,EnvL) APIst option =
  IntExtra.IterOp.iter k
    (fun ost => if ost <> None && callSt (oget ost) = None
              then let st = oget ost in 
                   let ecall = step (progSt st) (envSt st) (resSt st) in
                   omap st_from_step ecall else None) (Some st).

lemma stepPiter0
 (step : L -> EnvL -> apiRes_data option -> ((L,EnvL) ECall) option) 
 (k : int)
 (st : (L,EnvL) APIst) :
 k <= 0 =>
 stepPiter step k st = Some st.
proof. by move => ?; rewrite /stepPplus iter0. qed.

lemma nosmt stepPiter1  step (st:(L,EnvL) APIst):
 callSt st = None =>
 stepPiter step 1 st
 = omap st_from_step (step (progSt st) (envSt st) (resSt st)).
proof.
rewrite /stepPplus /progSt /envSt /resSt.
by rewrite iter1 /= => ->.
qed.

lemma nosmt stepPiterS_none  step k (s:(L,EnvL) APIst):
 stepPiter step k s = None =>
 stepPiter step (k+1) s = None.
proof.
move => ?; rewrite /progSt /envSt /resSt.
case: (0 <= k) => E.
 by rewrite IntExtra.IterOp.iterS //= H => *.
smt(iter0).
qed.

lemma nosmt stepPiterS_some  step k (s s':(L,EnvL) APIst) x:
 0 <= k =>
 stepPiter step k s = Some s' =>
 callSt s' = None =>
 step (progSt s') (envSt s') (resSt s') = Some x =>
 stepPiter step (k+1) s = Some (st_from_step x).
proof.
move => ???; rewrite /progSt /envSt /resSt.
rewrite IntExtra.IterOp.iterS //= => *.
by rewrite /st_from_step  H0 /= H1 H2.
qed.

lemma nosmt stepPiterS  step k (s : (L,EnvL) APIst):
 0 <= k =>
 stepPiter step (k+1) s = obind (stepPiter step 1) (stepPiter step k s).
proof.
elim/natind: k s => //=; first smt(stepPiter0).
move=> n Hn IH s H.
rewrite /stepPiter /= (_:2 = 1+1) 1:/# addzA iterS //= IH //=.
case: (stepPiter step n s) => //= st'.
case: (stepPiter step 1 st') => //= st''.
by rewrite iter1.
qed.

lemma nosmt stepPiter_lt  step (k i:int) (s s': (L,EnvL) APIst):
 0 <= i < k =>
 stepPiter step k s <> None =>
 stepPiter step i s = Some s' =>
 stepPiter step 1 s' <> None.
proof.
elim/natind: k; first smt().
move=> n Hn IH H.
rewrite stepPiterS //.
case: (i=n) => [->|E].
 by move=> ??; move: H0; rewrite H1.
pose a:= stepPiter step n s.
case: {2}a (eq_refl a) => [|a'] Ea //=; rewrite Ea //=.
move=> *; apply IH; smt(). 
qed.

lemma callSt_stepPiter  step k (s:(L,EnvL) APIst):
 callSt s <> None =>
 k <= 0 \/ stepPiter step k s = None.
proof.
move => ?.
elim/natind: k.
 by move=> ??; left.
move=> n Hn [?|?].
 have ->/=: n=0 by smt().
 by rewrite /stepPiter /= iter1 /= H.
by right; rewrite stepPiterS_none.
qed.

lemma nosmt stepPiter_det  step k1 k2 (s s1' s2': (L,EnvL) APIst):
 0 <= k1 =>
 0 <= k2 =>
 stepPiter step k1 s = Some s1' =>
 callSt s1' <> None =>
 stepPiter step k2 s = Some s2' =>
 callSt s2' <> None =>
 k1 = k2.
proof.
move => *.
case: (k1=k2) => // E.
case: (k1 < k2) => Hlt.
 move: (stepPiter_lt step k2 k1 s s1' _ _ _); first 3 smt().
 move: (callSt_stepPiter step k1 _ H2) => [?|?].
  move: H1; rewrite (_:k1=0) 1:/# stepPiter0 // => /someI ?.
  smt(callSt_stepPiter).
 smt(callSt_stepPiter).
move: (stepPiter_lt step k1 k2 s s2' _ _ _); first 3 smt().
move: (callSt_stepPiter step k2 _ H4) => [?|?].
 move: H3; rewrite (_:k2=0) 1:/# stepPiter0 // => /someI ?.
 smt(callSt_stepPiter).
smt(callSt_stepPiter).
qed.
 
end SinglePartyAPISemantics.
