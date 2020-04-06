(* Abstract class for protocol libraries *)
require import AllCore List.

(**
  An abstract protocol library provides a set of secure
  protocols that can be used to compute operations over
  confidential data.

  The library discloses protocols for secret operators,
  input, output and a special declassification command that
  reveals secret values. The last three protocols are concrete,
  whereas the secret operators are left underspecified as it
  is a general enough interface for protocols for secret operations.

  Besides dealing with secret inputs, protocols also tolerate plain
  values, that are assumed to be publicly known to all parties, as inputs.
  Protocols leave a communication trace resulting from party interaction.

  The library also provides a set of simulators that are
  part of the security assumpiton made over the multiparty
  protocols: the protocol is secure if there exists a simulator
  that is able to reproduce the communication trace and output
  shares of the corrupt parties.
*)
theory ProtocolLibrary.

  (** Number of parties involved in the protocol *)
  op n : int.

  (** Type of party identifiers *)
  type partyId_t. 

  (** Raw values *)
  type value_t.
  (** Secret inputs *)
  type inputs_t.
  (** Secret outputs *)
  type outputs_t.

  (** Messages *)
  type msg_data.
  (** Traces (lists of messages) *)
  type trace_t = msg_data list.

  (** Leakage used by simulators *)
  type leakage_t.

  (** Side information represents side information that is passed around
   (e.g. leakage or communication traces) *)
  type sideInfo_t = { leakage: leakage_t option ; trace: trace_t }.

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

end ProtocolLibrary.
