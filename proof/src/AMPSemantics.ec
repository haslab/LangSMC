(** Abstract class for multiparty semantics *)
require import AllCore List SmtMap.

require import ALanguage ASecretSharingScheme.

(**
  The multiparty semantics class is establishes how a program can
  be collaboratively animated. We define the multiparty semantics
  assuming that program evaluation is carried out by three computing
  nodes, each one holding a description of the program in pottentially
  different languages. We restrict the multiparty semantics
  to only three parties due to tool limitations. Nevertheless,
  having a three-party set is explanatory enough to demonstrate
  the concepts we want to explore in this work and the definitions
  here presented can easily be extended to other party configurations.

  Our semantics formalisation is based on adversarial code,
  influenced by the UC model. Program evaluation is managed
  by an environment, that can provide inputs to the program
  being interpreted and also collect outputs at any time.
  Furthermore, the environment can request the evaluation of
  the program in a small-step basis. This evaluation is carried
  out by an adversary, that, at a high-level, models the
  inside behaviour of the environment inside the program
  execution.

  The adversary has the possibility of either request some local party
  execution or a synchronised execution, where all parties, executing
  at the same time, have the ability to perform distributed protocols
  that require party interaction.

  Finally, the semantics here specified contemplates the possiblity
  of the execution disclosing the communication trace that is left by operations
  that result from the collaboration of parties.
*)
theory MultiPartySemantics.

  (** Language L1 *)
  clone import Language as L1.
  (** Language L2 *)
  clone import Language as L2.
  (** Language L3 *)
  clone import Language as L3.

  (** Communication trace *)
  type sideInfo_t.

  (** Party identifiers for multiparty semantics *)
  type partyId_t.

  (** Semantics interface *)
  (**
    The semantics interface discloses 6 procedures:
      - [init(P)] - initialises the evaluation with initial program P
      - [stepP(id)] - localy executes party [id]. This procedure
      is only used in multiparty semantics.
      - [stepS] - inside a multiparty semantics, executes the entire
      set of parties at the same time. This procedure should be used
      to perform operations that require party synchronisation in the
      multiparty setting.
      - [stepInput(x)] - processes the input [x] provided by the environment
      - [getOutput] - releases output to the environment
  *)
  module type Semantics = {
    proc init(P1 : L1.L, P2 : L2.L, P3 : L3.L) : unit
    proc stepP(id : partyId_t) : bool
    proc stepS() : sideInfo_t option
    proc setInput(x : secret_t) : bool
    proc getOutput() : secret_t option
  }.

  (** Environment semantics interface *)
  (**
    The environment semantics interface specifies how the
    environment interacts with the program evaluation. It
    discloses three procedures:
      - [stepInput(x)] - provides input [x] to the program
      - [getOutput] - collects output from the program
      - [activate] - activates the adversary so that it can
      procede with the actual program evaluation
  *)
  module type EnvSemInterface = {
    proc setInput(x: secret_t): bool
    proc getOutput(): secret_t option
    proc activate(): sideInfo_t option
  }.

  (** Output event type *)
  type output_event_t.

  (** Environment *)
  (** 
    The environment has oracle access to the environment 
    semantics interface in order to animate some program
    via the [animate] procedure
  *)
  module type Environment (ESI: EnvSemInterface) = {
    proc animate(): output_event_t 
  }.

  (** Adversary semantics interface *)
  (**
    The adversary semantics interface specifies how the adversary
    interacts with the program evaluation. It discloses two procedures:
      - [stepP(id)] - locally executes party [id]
      - [stepS] - performs a synchronised execution of the entire set
      of parties
  *)
  module type AdvSemInterface = {
    proc stepP(id: partyId_t): bool
    proc stepS(): sideInfo_t option
  }.

  (** Adversary *)
  (**
    The adversary has oracles access to the adversary
    semantics interface in order to execute one instruction of
    a program via the [step] procedure
  *)
  module type Adversary (ASI : AdvSemInterface) = {
    proc step() : sideInfo_t option
  }.

  (** Concrete environment semantics interface *)
  module EnvironmentSemanticsInterface (Sem : Semantics) (A : Adversary) = {
    include Sem [-init, setInput, getOutput]
    proc init = Sem.init
    proc setInput (x: secret_t): bool = {
      var r;
      r <@ Sem.setInput(x);
      return r;
    }
    proc getOutput(): secret_t option = {
      var r;
      r <@ Sem.getOutput();
      return r;
    }
    proc activate(): sideInfo_t option = {
      var r;
      r <@ A(Sem).step();
      return r;
    }
  }.

  (** General evaluation strategy *)
  module Eval(Sem : Semantics, Z : Environment, A : Adversary) = {
    proc eval(P1 : L1.L, P2 : L2.L, P3 : L3.L) = {
      var b;
      EnvironmentSemanticsInterface(Sem,A).init(P1,P2,P3);
      b <@ Z(EnvironmentSemanticsInterface(Sem,A)).animate();
      return (b);
    }
  }.

end MultiPartySemantics.
