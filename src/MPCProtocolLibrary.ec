(** Concrete protocol library working for share-based protocols *)
require import AllCore List Distr.

require import ASecretSharingScheme AProtocolLibrary.

(**
  The MPC protocol library provides a library of MPC protocols that work over
  shares generated by a secret sharing scheme.

  The protocol library here specified provides: a declassify protocol, an I/O
  interface and a protocol that securely computes a class of secret operators.
  Our goal is to identify the minimum security and correctness properties that
  these protocols need to enjoy in order to be employed in our secure computation
  framework. Therefore, we do not provide any concrete realisations of the
  protocols and instead make concrete assumptions on their security and correctness.
  This modular approach greatly reduces the complexity of future instantiations
  of our stack: because our proof evolves around the assumptions made,
  future instatiation will only need to assert that concrete protocols match
  the properties assumed, without the need to concern about how the protocols
  are inserted in the framework.

  Security is established by the equivalence between an honest protocol execution
  and a simulated one. The simulation of the protocol execution is done with
  recourse to some side information, representing visible data that is generated
  by the protocol. Then, together with the internal information (shares) of
  the corrupt parties, the simulation algorithm must be able to reproduce the
  communication trace of the corrupt parties.

  Finally, we define the correctness of the protocols by comparing their output
  against the expected functionality of the protocol. For protocols over secret
  operators, we provide an underspecified operator [sop_spec] that specifies the
  functional behaviour of such operators. For the remaining protocols of our suite,
  we provide concrete functionalities that those protocols must follow.
*)
theory MPCProtocolLibrary.

  (** Secret sharing scheme *)
  clone import SecretSharingScheme.

  (** Number of parties involved in the protocol *)
  op n = n.

  (** Type of party identifiers *)
  type partyId_t = partyId_t. 

  (** Raw values *)
  type value_t = value_t.
  (** Secret inputs *)
  type inputs_t = sharedValue_t.
  (** Secret outputs *)
  type outputs_t = sharedValue_t.

  (** Messages *)
  type msg_data.
  (** Traces (lists of messages) *)
  type trace_t = msg_data list.

  (** Leakage used by simulators *)
  type leakage_t = [
    | LeakedValue of value_t
    | LeakedShares of inputs_t
  ].

  (** Leakage 'get' methods *)
  op leakage_value (x: leakage_t) : value_t option =
    with x = LeakedValue v => Some v
    with x = LeakedShares _ => None.
  op leakage_shares (x: leakage_t) : inputs_t option =
    with x = LeakedValue v => None
    with x = LeakedShares s => Some s.

  (** Side information represents side information that is passed around
   (e.g. leakage or communication traces) *)
  type sideInfo_t = { leakage: leakage_t option ; trace: trace_t }.

  (** Side information constructors *)
  op Leak (v: value_t) : sideInfo_t =
    {| leakage = Some (LeakedValue v); trace = [] |}.
  op CorruptedShares (s: inputs_t) : sideInfo_t =
    {| leakage = Some (LeakedShares s); trace = [] |}.
  op Trace (l: leakage_t option) t = {| leakage=l; trace=t |}.

  (** Gets the leakage from the side information *)
  op sideInfo_leak (x: sideInfo_t) : value_t option = obind leakage_value x.`leakage.
  (** Gets the corrupted shares from the side information *)
  op sideInfo_io (x: sideInfo_t) : inputs_t option = obind leakage_shares x.`leakage.
  (** Gets the communication trace from the side information *)
  op sideInfo_trace (x: sideInfo_t) : trace_t = x.`trace.

  (** Extracts the leaked value on a declassify sideInfo *)
  op leakedValue (l: sideInfo_t): value_t = oget (sideInfo_leak l).
  (** Extracts the input corrupted shares from a input sideInfo *)
  op corruptedShares (l: sideInfo_t): inputs_t = oget (sideInfo_io l).

  (** Secret operators *)
  type sop_t.

  (** Functionality of secret operators *)
  op sop_spec (sop: sop_t, pargs: value_t list, sargs: value_t list) : value_t * leakage_t option.

  (** Protocols *)

  (** Declassification protocol *)
  op [lossless] prot_declass(a: inputs_t): (value_t * sideInfo_t) distr.
  (** Input protocol *)
  op [lossless] prot_in(inp: inputs_t): sideInfo_t distr.
  (** Output protocol *)
  op [lossless] prot_out(a: inputs_t): (outputs_t * sideInfo_t) distr.
  (** Secret operator protocol *)
  op [lossless] prot_sop(sop: sop_t, pargs: value_t list, sargs: inputs_t list)
        : (outputs_t * sideInfo_t) distr.

  (** Simulators *)

  (** Declassification simulator *)
  op [lossless] sim_declass(a: inputs_t, l: leakage_t): trace_t distr.
  (** Input simulator *)
  op [lossless] sim_in(x: leakage_t): trace_t distr.
  (** Output simulator *)
  op [lossless] sim_out(x: inputs_t, y: leakage_t): trace_t distr.
  (** Secret operator simulator *)
  op [lossless] sim_sop(sop: sop_t, pargs: value_t list, sargs: inputs_t list, l: leakage_t option)
        : (outputs_t * trace_t) distr.

  clone import ProtocolLibrary with
    op n = n,
    type partyId_t = partyId_t,
    type value_t = value_t,
    type inputs_t = inputs_t,
    type outputs_t = outputs_t,
    type msg_data = msg_data,
    type leakage_t = leakage_t,
    type sideInfo_t = sideInfo_t,
    type sop_t = sop_t,
    op sop_spec = sop_spec,
    op prot_declass = prot_declass,
    op prot_in = prot_in,
    op prot_out = prot_out,
    op prot_sop = prot_sop,
    op sim_declass = sim_declass,
    op sim_in = sim_in,
    op sim_out = sim_out,
    op sim_sop = sim_sop
  proof *.
  realize prot_declass_ll. by apply prot_declass_ll. qed.
  realize prot_in_ll. by apply prot_in_ll. qed.
  realize prot_out_ll. by apply prot_out_ll. qed.
  realize prot_sop_ll. by apply prot_sop_ll. qed.
  realize sim_declass_ll. by apply sim_declass_ll. qed.
  realize sim_in_ll. by apply sim_in_ll. qed.
  realize sim_out_ll. by apply sim_out_ll. qed.
  realize sim_sop_ll. by apply sim_sop_ll. qed.
    
  (* Correctness and Security Assumptions are captured by
  adequate pRHL assertions                                   *)
module APIsec = {
 proc prot_declass(a: sharedValue_t): value_t * sideInfo_t = {
    var x;
    x <$ prot_declass a;
    return x;
 }
 proc sim_declass(a: inputs_t, l: leakage_t): value_t * sideInfo_t = {
   var t;
   t <$ sim_declass a l;
   return (oget (leakage_value l), Trace (Some l) t);
 }
 proc prot_in(a: sharedValue_t): sideInfo_t = {
   var x;
   x <$ prot_in a;
   return x;
 }
 proc sim_in(l: leakage_t): sideInfo_t = {
   var x;
   x <$ sim_in l;
   return Trace (Some l) x;
 }
 proc prot_out(a: sharedValue_t): sharedValue_t * sideInfo_t = {
   var x;
   x <$ prot_out a;
   return x;
 }
 proc sim_out(a: sharedValue_t, l: leakage_t): sideInfo_t = {
   var t;
   t <$ sim_out a l;
   return Trace (Some l) t;
 }
 proc spec_out(a: sharedValue_t): sharedValue_t * sideInfo_t = {
   var x, y, l, tr;
   x <$ nshr n (unshr a);
   y <- take t x;
   l <- LeakedShares y;
   tr <@ sim_out (take t a, l);
   return (x, tr);
 }
 proc prot_sop(o: sop_t, pargs: value_t list, sargs: sharedValue_t list): sharedValue_t * sideInfo_t = {
   var x;
   x <$ prot_sop o pargs sargs;
   return x;
 }
 proc sim_sop(o: sop_t, pargs: value_t list, sargs: sharedValue_t list, l: leakage_t option): sharedValue_t * sideInfo_t = {
   var x,t;
   (x,t) <$ sim_sop o pargs sargs l;
   return (x, Trace l t);
 }

}.

axiom assumption_declass aa ll:
 equiv [ APIsec.sim_declass ~ APIsec.prot_declass:
         aa = a{2} /\ ll = l{1} /\
         take n a{2} = a{1} /\
         l{1} = LeakedValue (unshr a{2})
         ==>
         ={res} /\
         res{2}.`1 = unshr aa /\ res{2}.`2.`leakage = Some ll
       ].

axiom assumption_in ll:
 equiv [ APIsec.sim_in ~ APIsec.prot_in:
         ll = l{1} /\
         l{1} = LeakedShares (take n a{2})
         ==>
         ={res} /\ res{2}.`leakage = Some ll
       ].

axiom assumption_sop oo pp aa ll:
 equiv [ APIsec.sim_sop ~ APIsec.prot_sop:
         ={o, pargs} /\
         aa = sargs{2} /\ 
         ll = l{1} /\
         l{1} = (sop_spec oo pp (map unshr aa)).`2 /\
         map (take n) sargs{2} = sargs{1}
         ==>
         ={res} /\
         unshr res{2}.`1 = (sop_spec oo pp (map unshr aa)).`1 /\
         res{2}.`2.`leakage = ll
       ].

(* the security notion for [prot_out] is stronger than for the
 remaining protocolos. The assumption resorts to an auxiliary
 procedure.                                                    *) 
axiom assumption_out:
 equiv [ APIsec.spec_out ~ APIsec.prot_out:
         ={a} ==> ={res} ].

end MPCProtocolLibrary.
