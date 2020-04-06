(** Abstract class for single party semantics *)
require import AllCore List SmtMap.

require import ALanguage ASecretSharingScheme.

(**
  The single pary semantics class is parameterised by a language and
  should establish how programs written in that language
  are animated.

  Our semantics formalisation is based on adversarial code,
  influenced by the UC model. Program evaluation is managed
  by an environment, that can provide inputs to the program
  being interpreted and also collect outputs at any time.
  Furthermore, the environment can request the evaluation of
  the program in a small-step basis. This evaluation is carried
  out by an adversary, that, at a high-level, models the
  inside behaviour of the environment inside the program
  execution.

  The adversary has the possibility of requesting the execution
  of one program statement at a time. The semantics also contemplates 
  the possiblity some side information being leaked by language instructions.
*)
theory SinglePartySemantics.

  (** Language *)
  clone import Language.

  (** Side information *)
  type sideInfo_t.

  (** Semantics interface *)
  (**
    The semantics interface discloses 6 procedures:
      - [init(P)] - initialises the evaluation with initial program P
      - [step] - sequential semantics procedures, that executes one
      instruction of the program.
      - [stepInput(x)] - processes the input [x] provided by the environment
      - [getOutput] - releases output to the environment
  *)
  module type Semantics = {
    proc init(P : L) : unit
    proc step() : sideInfo_t option
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
    proc step(): sideInfo_t option
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
    proc init = Sem.init
    proc setInput(x: secret_t): bool = {
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
    proc eval(P : L) = {
      var b;
      EnvironmentSemanticsInterface(Sem,A).init(P);
      b <@ Z(EnvironmentSemanticsInterface(Sem,A)).animate();
      return (b);
    }
  }.

end SinglePartySemantics.
